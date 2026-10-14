#!/usr/bin/env python3
"""Build a separate client against an exported library, without research imports."""

import argparse
from pathlib import Path
import subprocess


CLIENT = r'''(*  Title:      Library_Client.thy
    Author:     Tang Ziyi
*)

section \<open>External Library Client\<close>

theory Library_Client
  imports "Set_Coded_Turing_Machines.Turing_Halting_Codes"
begin

text \<open>This program halts on a blank cell and otherwise leaves the
configuration unchanged. The client proves both outcomes, transfers them
to another finite tape representation, and characterises the truth of a
formula given only its numerical code. No example or research theory is
imported, and the internal halting formula is not unfolded.\<close>

definition blank_guard :: i where
  "blank_guard \<equiv>
    [\<langle>nop,final_state\<rangle>,\<langle>nop,initial_state\<rangle>]"

lemma blank_guard_type [TC]: "blank_guard \<in> tm_machine"
  unfolding blank_guard_def tm_machine_def instruction_def by typecheck

lemma blank_guard_empty_step:
  "tm_step(blank_guard,initial_config([])) = \<langle>final_state,\<langle>[],[]\<rangle>\<rangle>"
  by (simp add: blank_guard_def fetch_def slot_def)

lemma blank_guard_nonempty_step:
  assumes "n \<in> nat"
  shows "tm_step(blank_guard,initial_config(numeral_input(succ(n)))) =
    initial_config(numeral_input(succ(n)))"
  using assms by (simp add: blank_guard_def fetch_def slot_def numeral_input_def)

lemma blank_guard_nonempty:
  assumes n: "n \<in> nat"
  shows "\<not> halts_on(blank_guard,numeral_input(succ(n)))"
  by (rule not_halts_on_invariant
        [where I="\<lambda>c. c = initial_config(numeral_input(succ(n)))"])
    (simp, simp only: blank_guard_nonempty_step[OF n], simp)

theorem blank_guard_halts_iff:
  assumes n: "n \<in> nat"
  shows "halts_on(blank_guard,numeral_input(n)) \<longleftrightarrow> n = 0"
proof (cases "n = 0")
  case True
  have "halts_on(blank_guard,[])"
    by (rule halts_onI[OF blank_guard_type, where n=1])
      (simp, simp, simp only: steps_succ steps_0 blank_guard_empty_step fst_conv)
  with True show ?thesis by (simp add: numeral_input_def)
next
  case False
  from n False obtain k where "k \<in> nat" "n = succ(k)" by (auto elim: natE)
  with blank_guard_nonempty show ?thesis by auto
qed

theorem blank_guard_padded_iff:
  assumes n: "n \<in> nat" and k: "k \<in> nat"
  shows "halts_on(blank_guard,numeral_input(n) @ repeat(blank_symbol,k))
    \<longleftrightarrow> n = 0"
proof -
  have x: "numeral_input(n) \<in> list(symbol)" by (rule numeral_input_type[OF n])
  have padding: "repeat(blank_symbol,k) \<in> list(symbol)" using k by typecheck
  have eq: "half_tape_eq(numeral_input(n) @ repeat(blank_symbol,k),numeral_input(n))"
    using half_tape_eq_append[OF x half_tape_eq_blank_repeat[OF k]] x by simp
  from halts_on_half_tape_eq_iff[OF blank_guard_type _ x eq]
    x padding blank_guard_halts_iff[OF n] show ?thesis by simp
qed

theorem blank_guard_sentence_iff:
  assumes model: "transitive_zf_model(A)" and n: "n \<in> nat"
  shows "(A, [] \<Turnstile> halt_sentence(blank_guard,numeral_input(n)))
    \<longleftrightarrow> n = 0"
  using sats_halt_sentence_iff[OF model blank_guard_type numeral_input_type[OF n]]
    blank_guard_halts_iff[OF n] by simp

theorem blank_guard_padded_sentence_iff:
  assumes model: "transitive_zf_model(A)" and n: "n \<in> nat" and k: "k \<in> nat"
  shows "(A, [] \<Turnstile> halt_sentence(blank_guard,
      numeral_input(n) @ repeat(blank_symbol,k))) \<longleftrightarrow> n = 0"
proof -
  have x: "numeral_input(n) \<in> list(symbol)" by (rule numeral_input_type[OF n])
  have padding: "repeat(blank_symbol,k) \<in> list(symbol)" using k by typecheck
  have eq: "half_tape_eq(numeral_input(n) @ repeat(blank_symbol,k),numeral_input(n))"
    using half_tape_eq_append[OF x half_tape_eq_blank_repeat[OF k]] x by simp
  from sats_halt_sentence_half_tape_eq_iff[OF model blank_guard_type _ x eq]
    x padding blank_guard_sentence_iff[OF model n] show ?thesis by simp
qed

theorem blank_guard_code_iff:
  assumes model: "transitive_zf_model(A)" and n: "n \<in> nat"
    and p: "p \<in> formula"
    and code: "formula_code(p) =
      pr_machine_input_sentence_code`[encode_machine(blank_guard),n]"
  shows "(A, [] \<Turnstile> p) \<longleftrightarrow> n = 0"
  using sats_machine_input_sentence_code_iff[OF model
      encode_machine_natural[OF blank_guard_type] n p code]
    decode_encode_machine[OF blank_guard_type] blank_guard_halts_iff[OF n] by simp

end
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--isabelle", required=True, type=Path)
    parser.add_argument("--entry", required=True, type=Path)
    parser.add_argument("--directory", required=True, type=Path)
    args = parser.parse_args()
    entry = args.entry.resolve()
    if not (entry / "ROOT").is_file():
        raise SystemExit("Entry directory must contain ROOT")
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=False)
    (directory / "Library_Client.thy").write_text(CLIENT)
    (directory / "ROOT").write_text(
        "session Library_Client = Set_Coded_Turing_Machines +\n"
        "  options [timeout=300]\n  theories Library_Client\n")
    result = subprocess.run([
        str(args.isabelle.resolve()), "build", "-v", "-j", "1", "-o", "threads=2",
        "-d", str(entry), "-D", str(directory)])
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
