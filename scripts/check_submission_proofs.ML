(* Check endpoints and the complete canonical entry proof closure. *)

fun check_submission_oracles description thms =
  if null (Thm_Deps.all_oracles thms) then ()
  else error ("Oracle dependency in " ^ description);

local
  val entry = "Set_Coded_Halting_Invariance_ZF.";
  val endpoints =
    [("Turing_Halting_Formula", "M_ZF1_trans.sats_halt_fm"),
     ("Turing_Halting_Sentences", "M_ZF1_trans.sats_halt_sentence_iff"),
     ("Turing_Effective_Invariance", "pr_reduces_invariance"),
     ("Turing_Halting_Formula", "transitive_model_halt_fm_iff"),
     ("Turing_Halting_Sentences", "sats_halt_sentence_iff"),
     ("Turing_Rejection", "self_halting_not_tm_decidable"),
     ("Formula_Coding", "formula_code_injective"),
     ("Turing_Effective_Invariance", "self_halting_pr_many_one_invariance"),
     ("Turing_Effective_Invariance", "nonhalting_pr_many_one_invariance")];

  fun check_theorem (theory_name, name) =
    let
      val thy = Thy_Info.get_theory (entry ^ theory_name);
      val thm = Global_Theory.get_thm thy name;
      val _ = if null (Thm.hyps_of thm) then ()
        else error ("Undischarged theorem hypotheses in " ^ name);
      val _ = check_submission_oracles name [thm];
    in writeln ("Checked " ^ name) end;

  val theories = filter (String.isPrefix entry) (Thy_Info.get_names ());
  val _ = if length theories = 19 then ()
    else error "Expected nineteen canonical entry theories";
  val facts = maps (fn name => Global_Theory.all_thms_of
    (Thy_Info.get_theory name) false) theories;
  val unique = Thm_Name.Table.dest
    (fold Thm_Name.Table.update facts Thm_Name.Table.empty);
in
  val _ = List.app check_theorem endpoints;
  val _ = check_submission_oracles "the entry proof closure" (map #2 unique);
  val _ = writeln ("Checked " ^ string_of_int (length unique) ^
    " named facts across nineteen entry theories, including imported dependencies, without oracle dependencies");
end;
