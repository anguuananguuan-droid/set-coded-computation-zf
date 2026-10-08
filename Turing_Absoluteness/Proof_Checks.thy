theory Proof_Checks
  imports Turing_Decidable_Sets
begin

ML \<open>
  val main_results =
    [@{thm transitive_model_halt_fm_iff},
     @{thm arity_halt_fm_eq},
     @{thm sats_halt_sentence_iff},
     @{thm arity_halt_sentence},
     @{thm blank_halting_or_CH_invariant_iff},
     @{thm invariant_index_set_eq_self_halting},
     @{thm invariant_index_set_not_tm_decidable},
     @{thm tm_decidable_in_transitive_model}];
  val oracles = Thm_Deps.all_oracles main_results;
  val _ = if null oracles then () else error "Main results depend on an oracle";
\<close>

end
