# Library guide

## 1 Imports

The public session is `Set_Coded_Turing_Machines`. A client theory chooses
the smallest interface it needs.

```isabelle
theory My_Machine
  imports "Set_Coded_Turing_Machines.Turing_Machine"
begin

end
```

Use `Turing_Tape` for observational equality, `Turing_Coding` for numerical
machine codes, `Turing_Halting_Sentences` for internal satisfaction, and
`Turing_Halting_Codes` for primitive-recursive sentence construction.
Each extends the machine interface. The example theories are clients, not
imports required by the definitions.

A client directory with this theory uses the following ROOT.

```text
session My_Machines = Set_Coded_Turing_Machines +
  options [timeout=300]
  theories
    My_Machine
```

With the AFP dependency registered as described in [Build](BUILD.txt), run
`isabelle build -d /absolute/path/to/this/repository -D /absolute/path/to/client`.
The packaged session has an AFP dependency for its model interface.
The separate computation check verifies the operational theories without AFP.

## 2 Machine conventions

A machine is a finite list of instructions. Each instruction is a pair of
an action and a natural-number next state. The symbols are 0 and 1, with 0
blank. The initial state is 1 and the final state is 0. Actions write 0,
write 1, move left, move right, or leave the tape unchanged. Writing and
moving are separate transitions.

For positive state q and symbol b, `fetch` reads instruction index
`2 * (q - 1) + b`. A missing entry leaves the tape unchanged and enters
state 0. In state 0, the entire configuration is unchanged by further steps.
A machine may contain an odd number of entries. No completeness premise on
its instruction table is required.

A configuration pairs a state with a tape. The tape pairs two finite symbol
lists. The left list starts immediately left of the head and extends
outwards. The right list starts at the scanned cell. Cells beyond either
list are blank. `initial_config(x)` has state 1, an empty left list, and
input x on the right. `numeral_input(n)` is a list of n ones.

The public operations are `tm_step(P,c)`, `steps(P,c,n)`, and `halts_on(P,x)`.
Their domains are `tm_machine`, `configuration`, `nat`, and `list(symbol)`.
The halting predicate includes machine and input validity. Other equations
should be used with the domain premises in their statements. Set-theoretic
definitions do not reject ill-formed arguments through a programming type
system.

## 3 Proving a program

[Turing_Examples](../thys/Set_Coded_Turing_Machines/Turing_Examples.thy)
is a complete checked example. The machine has two instructions.

```isabelle
[\<langle>write_one,final_state\<rangle>, \<langle>move_right,initial_state\<rangle>]
```

The machine scans right through a unary input, writes one at the first
blank, and halts on the newly written cell. Its proof gives the following
configuration after n + 1 steps.

```text
state       0
left        numeral_input(n)
right       [one_symbol]
```

The head is at the new rightmost one. This is a specified tape result, not
an implicit convention that the output must start under the original head.

`scan_append_loop` proves the scan invariant with an arbitrary left list.
`scan_append_result` gives the final configuration. `scan_append_halts`
applies `halts_onI` to the result. The proof uses `steps_add` to join a
first step to the remaining run.

Useful general facts are `step_type`, `steps_type`, `steps_add`,
`steps_final_absorb`, and `halts_onI`. The theorem
`halts_on_iff_finite_run` supplies a finite function of configurations
when a subsequent argument needs an explicit execution witness.

## 4 Tape observations

`[1]` and `[1,0,0]` are different finite lists with identical observed
contents. `half_tape_eq` compares all natural positions using blank beyond
the represented end. `tape_eq` compares both halves. `config_eq` also
requires well-formed configurations and equal states.

`steps_config_eq` preserves configuration equivalence after any common
finite number of steps of a well-formed machine. `config_eq_observe`
recovers the state and scanned symbol. These relations do not identify
head shifts. Raw list equality remains available for exact storage results.

`scan_append_padded_result` transfers the example to an input with an extra
stored blank. It reuses the operational result through `steps_config_eq`.
The tape span lemmas describe the nondecreasing storage length, explaining
why tape contents and literal storage size are different specifications.

## 5 Internal halting sentences

For a well-formed P and x, `halt_fm` is a formula with environment `[P,x]`.
`halt_sentence(P,x)` is closed and names the two finite objects internally.
For a transitive ZF set model A, `sats_halt_sentence_iff` states

```text
(A, [] satisfies halt_sentence(P,x)) iff halts_on(P,x).
```

The prerequisites are `transitive_zf_model(A)`, `P in tm_machine`, and
`x in list(symbol)`. The formula is not a recogniser for arbitrary sets as
machines or inputs. The theorem does not assert model existence.
The qualified `M_ZF1_trans.sats_halt_sentence_iff` is available when working
in that weaker locale. Choice is not needed.

[Turing_Halting_Examples](../thys/Set_Coded_Turing_Machines/Turing_Halting_Examples.thy)
uses the example's halting proof to establish its internal sentence. It
calls the public satisfaction theorem without unfolding the internal formula.

## 6 Numerical codes

`decode_encode_machine` recovers a valid machine from its code.
`decode_machine` is total on natural numbers and normalises invalid action
fields. It is not injective on all natural numbers. `machine_numbering_bij`
is a bijection only on the canonical machine codes.

`formula_code_injective` states injectivity on well-formed formulas.
`pr_halt_sentence_code_in_prim_rec` certifies the numerical construction of
a self-input halting sentence. `pr_halt_sentence_code_apply` identifies its
value with the code of
`halt_sentence(decode_machine(e),numeral_input(e))` for natural e.
The primitive-recursive function is applied to `[e]`; its equation also
allows unused natural-number arguments after the first.

This interface certifies the self-input construction. It does not provide
a general primitive-recursive-to-machine compiler or an effective
translation of arbitrary arithmetic sentences.
