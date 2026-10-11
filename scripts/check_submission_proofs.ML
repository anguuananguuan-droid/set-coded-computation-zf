(* Proof dependency check for the exported submission heap. *)

fun check_submission_oracles description thms =
  if null (Thm_Deps.all_oracles thms) then ()
  else error ("Oracle dependency in " ^ description);

local
  val thy =
    Thy_Info.get_theory "Set_Coded_Halting_Invariance_ZF.Turing_Effective_Invariance";
  val endpoints =
    ["transitive_model_halt_fm_iff", "sats_halt_sentence_iff",
     "self_halting_not_tm_decidable", "formula_code_injective",
     "self_halting_pr_many_one_invariance", "nonhalting_pr_many_one_invariance"];

  fun check_theorem name =
    let
      val thm = Global_Theory.get_thm thy name;
      val _ = if null (Thm.hyps_of thm) then ()
        else error ("Undischarged theorem hypotheses in " ^ name);
      val _ = check_submission_oracles name [thm];
    in writeln ("Checked " ^ name) end;

  val facts = map #2 (Global_Theory.all_thms_of thy false);
in
  val _ = List.app check_theorem endpoints;
  val _ = check_submission_oracles "the submission proof closure" facts;
  val _ = writeln ("Checked " ^ string_of_int (length facts) ^
    " named facts, including imported dependencies, without oracle dependencies");
end;
