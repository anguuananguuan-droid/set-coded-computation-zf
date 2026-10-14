(* Check endpoints and the complete canonical entry proof closure. *)

fun check_submission_oracles description thms =
  if null (Thm_Deps.all_oracles thms) then ()
  else error ("Oracle dependency in " ^ description);

local
  val entry = "Set_Coded_Turing_Machines.";
  val endpoints =
    [("Turing_Machine", "halts_on_iff_finite_run"),
     ("Turing_Machine", "steps_invariant"),
     ("Turing_Machine", "not_halts_on_invariant"),
     ("Turing_Tape", "steps_config_eq"),
     ("Turing_Tape", "halts_on_half_tape_eq_iff"),
     ("Turing_Examples", "scan_append_result"),
     ("Turing_Examples", "scan_append_padded_result"),
     ("Turing_Coding", "decode_encode_machine"),
     ("Turing_Halting_Formula", "M_ZF1_trans.sats_halt_fm"),
     ("Turing_Halting_Formula", "transitive_model_halt_fm_iff"),
     ("Turing_Halting_Sentences", "M_ZF1_trans.sats_halt_sentence_iff"),
     ("Turing_Halting_Sentences", "sats_halt_sentence_iff"),
     ("Turing_Halting_Sentences", "sats_halt_sentence_half_tape_eq_iff"),
     ("Formula_Coding", "formula_code_injective"),
     ("Turing_Halting_Codes", "pr_machine_input_sentence_code_in_prim_rec"),
     ("Turing_Halting_Codes", "pr_machine_input_sentence_code_apply"),
     ("Turing_Halting_Codes", "pr_machine_input_sentence_code_iff"),
     ("Turing_Halting_Codes", "sats_machine_input_sentence_code_iff"),
     ("Turing_Halting_Codes", "pr_halt_sentence_code_in_prim_rec"),
     ("Turing_Halting_Codes", "pr_halt_sentence_code_apply"),
     ("Turing_Halting_Examples", "scan_append_sentence")];

  fun check_theorem (theory_name, name) =
    let
      val thy = Thy_Info.get_theory (entry ^ theory_name);
      val thm = Global_Theory.get_thm thy name;
      val _ = if null (Thm.hyps_of thm) then ()
        else error ("Undischarged theorem hypotheses in " ^ name);
      val _ = check_submission_oracles name [thm];
    in writeln ("Checked " ^ name) end;

  val theories = filter (String.isPrefix entry) (Thy_Info.get_names ());
  val _ = if length theories = 17 then ()
    else error "Expected seventeen canonical entry theories";
  val facts = maps (fn name => Global_Theory.all_thms_of
    (Thy_Info.get_theory name) false) theories;
  val unique = Thm_Name.Table.dest
    (fold Thm_Name.Table.update facts Thm_Name.Table.empty);
in
  val _ = List.app check_theorem endpoints;
  val _ = check_submission_oracles "the entry proof closure" (map #2 unique);
  val _ = writeln ("Checked " ^ string_of_int (length unique) ^
    " named facts across seventeen entry theories, including imported dependencies, without oracle dependencies");
end;
