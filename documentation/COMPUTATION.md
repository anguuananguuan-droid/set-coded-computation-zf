# Computation in Isabelle/ZF

## 1 Machine and execution

A machine is a finite list of instructions. Each instruction gives an action
and the next state. The tape has symbols 0 and 1, with 0 as blank. State 1
is initial and state 0 is final. There are five actions, write 0, write 1,
move left, move right, and leave the tape unchanged. Writing and moving are
separate steps.

Two entries are assigned to each nonfinal state, one for each scanned symbol.
For state q greater than 0 and symbol b, the list index is
`2 * (q - 1) + b`. A missing entry leaves the tape unchanged and enters state
0. Execution in state 0 leaves the entire configuration unchanged.

The tape is represented by two finite lists. The left list starts with the
cell immediately left of the head and proceeds outwards. The right list
starts with the scanned cell and proceeds to the right. Unrepresented cells
are blank. A configuration consists of a state and this pair of lists.

For example, take the two instruction entries below. Both belong to state 1.
The first handles a scanned 0 and the second a scanned 1.

```text
M = [<write_one, 0>, <write_one, 0>]

                         state     left     right
initial configuration        1       []        []
after one step               0       []       [1]
```

On a blank tape this machine writes 1 and halts without moving the head.
The displayed notation abbreviates the nested pairs used by the source.
This example is a direct evaluation of the definitions.

[Turing_Machine.thy](../Turing_Machines_ZF/Core/Turing_Machine.thy) defines
`step`, its finite iteration `steps`, and `halts_on`. The theorem
`halts_on_iff_finite_run` identifies halting with the existence of a finite
sequence of configurations that starts at the input configuration, obeys
every transition, and ends in state 0. The sequence is represented as a
function on a finite initial segment of the natural numbers.

All these objects are sets in Isabelle/ZF. Membership in `machine`, `tape`,
and `configuration` expresses their well formedness. The core does not use
an Isabelle/HOL machine datatype or assume the existence of a transitive
model of ZFC.

## 2 Tape contents

The lists `[1]` and `[1,0,0]` represent the same right half of a tape. Both
place 1 under the head and blanks everywhere to its right. They are distinct
lists, but a machine cannot distinguish their contents. By contrast,
`[1,0]` and `[0,1]` place the 1 at different positions relative to the head
and are distinguishable.

[Turing_Tape.thy](../Turing_Machines_ZF/Core/Turing_Tape.thy) defines
`half_tape_eq` by equality at every natural position, taking an out of range
entry as blank. `tape_eq` compares both halves, and `config_eq` also requires
equal states. The theorem `steps_config_eq` proves that equivalent
configurations remain equivalent after any common finite number of steps
of the same machine.

This distinction matters for numerical output. In this machine model, the
total length of the two stored lists never decreases. Erasing two 1s can
leave `[0,0]`, but cannot leave a literally empty representation of the whole
tape. A specification demanding that literal result would exclude ordinary
erasure. `steps_span_mono` proves the length property. Observational equality
allows the intended blank output to be represented without requiring the
lists themselves to shrink.

## 3 Codes and evaluation

[Turing_Coding.thy](../Turing_Machines_ZF/Core/Turing_Coding.thy) builds codes
for pairs of natural numbers, finite lists, instructions, and machines.
Every machine has a canonical natural number code. Decoding that code
recovers the machine, as stated by `decode_encode_machine`. The theorem
`machine_numbering_bij` gives a bijection between machines and the set of
canonical machine codes.

The decoder also accepts every natural number. An instruction with an
invalid action field is replaced by the default instruction. Thus the
decoder is total and reaches every machine, although different arbitrary
numbers can decode to the same machine. This permits a halting question to
be asked of every natural number without a separate validity test.

[Turing_Code_Operations.thy](../Turing_Machines_ZF/Core/Turing_Code_Operations.thy)
provides projections and operations on coded lists.
[Turing_Evaluator.thy](../Turing_Machines_ZF/Core/Turing_Evaluator.thy) uses
them to compute the next configuration code directly. For a natural machine
code e and a well formed configuration c, `code_step_correct` proves the
following equality.

```text
code_step(e, encode_configuration(c))
  = encode_configuration(step(decode_machine(e), c))
```

The theorem `code_steps_correct` extends this equality to any supplied
natural number of steps. `code_halts_at_correct` then relates the numeric
final state test to the machine's final state. These are exact equalities
for the stored configurations, including their finite lists.

[Turing_Primrec.thy](../Turing_Machines_ZF/Core/Turing_Primrec.thy) gives
primitive-recursive certificates for the numerical pairing and list-code
operations. [Turing_Evaluator_Primrec.thy](../Turing_Machines_ZF/Core/Turing_Evaluator_Primrec.thy)
certifies one-step and bounded finite-step evaluation. For example,
`pr_code_steps_in_prim_rec` proves membership in the formal class of
primitive-recursive functions, and `pr_code_steps_apply` identifies the
certificate's output with `code_steps`.

The evaluator is a mathematical function on numbers. The development has
not constructed a finite Turing machine that implements it. Such a
construction would be an additional universality result.

## 4 Self input halting

[Turing_Decidability.thy](../Turing_Machines_ZF/Core/Turing_Decidability.thy)
represents a natural number n by n consecutive 1s on an otherwise blank
tape. A machine accepts when it halts scanning 1, and rejects when it halts
scanning 0. A decider must halt on every such input and give the correct
answer.

The set `self_halting` contains exactly those numbers e for which
`decode_machine(e)` halts on the numeral input for e. To prove that no
machine decides this set, the development constructs a rejecting machine
from any proposed decider D.

[Turing_Rejection.thy](../Turing_Machines_ZF/Core/Turing_Rejection.thy)
chooses a fresh control state and redirects halting transitions to it.
In that state, a scanned 0 leads to halting and a scanned 1 leads to a loop.
The construction also handles missing instructions, whose original
behaviour was to halt. It produces a finite instruction list and proves
that the new machine halts exactly when D rejects.

Suppose D decided `self_halting`. Let Q be its rejecting machine and let q
be the canonical code of Q. Then Q halts on q exactly when D rejects q.
Since D is a decider, it rejects q exactly when Q does not halt on q.
The contradiction rules out D.

The abstract argument in `Turing_Decidability` assumes the rejecting
transformation through a locale, an interface of stated hypotheses.
`Turing_Rejection` constructs the transformation and proves those hypotheses.
Its theorem `self_halting_not_tm_decidable` therefore establishes
`~ tm_decidable(self_halting)` without an unproved transformation assumption.
It concerns the decision semantics and machine model defined here.

## 5 Bounded workspace

Correct execution on an otherwise blank tape does not by itself protect data
stored nearby. A machine can move beyond its input and overwrite a saved
cell. A preservation theorem needs an explicit condition that keeps those
cells outside the active computation.

[Turing_Workspace.thy](../Turing_Machines_ZF/Core/Turing_Workspace.thy)
appends a saved list to the outer end of each workspace half. This is the
operation `frame_config`. It adds ordinary tape data, without changing the
instruction set or giving the machine a new boundary test.

If both represented halves have at least n cells, `steps_preserve_frame`
proves that n steps with the saved lists attached have exactly the same
result as n steps in the workspace followed by reattaching the original
saved lists. Their contents remain unchanged. The proof uses the fact that
one step can consume at most one cell from either half.

For an arbitrary configuration, `pad_config` appends n blank cells to each
half before adding the saved data. Padding preserves the represented tape
contents. `bounded_workspace_history` combines this observation with frame
preservation. For every k at most n, the saved lists are intact and the
workspace computation agrees observationally with the original unpadded
computation.

For example, adding ten blanks to each half protects the saved lists through
the first ten steps of any machine. The caller supplies ten as a bound on
the interval being considered. The theorem does not determine when the
machine halts or guarantee protection for an eleventh step. It also does not
assert that the whole framed tape has the same contents as the unframed
tape, since the frame can contain nonblank data.

## 6 Dependencies and scope

The ten theories form one independent
[session](../Turing_Machines_ZF/Core/ROOT). Within that session, the direct
imports are as follows. Each line names a theory followed by its import.

```text
Turing_Machine            ZF
Turing_Tape               Turing_Machine
Turing_Coding             Turing_Machine
Turing_Code_Operations    Turing_Coding
Turing_Primrec            Turing_Code_Operations, ZF-Induct.Primrec
Turing_Evaluator          Turing_Code_Operations
Turing_Evaluator_Primrec  Turing_Evaluator, Turing_Primrec
Turing_Decidability       Turing_Coding
Turing_Rejection          Turing_Decidability
Turing_Workspace          Turing_Tape
```

The undecidability proof uses machine semantics, coding, decision semantics,
and the concrete rejection transformation. Numeric evaluation is a separate
branch of the coding development. Workspace preservation is a consequence
of machine and tape semantics. Neither is a premise of the diagonal proof.

The five action instruction format follows the operational model of the
AFP entry
[Universal Turing Machine](https://www.isa-afp.org/entries/Universal_Turing_Machine.html).
The core imports Isabelle/ZF, its bundled ZF-Induct session, and its own
theories. It does not inherit
the HOL entry's universality theorem. No simulation theorem between this
instruction format and a different machine format is claimed.

[Build instructions](BUILD.txt) reproduce the proofs.
[Research extensions](RESEARCH.md) describes the remaining program and model
theories. Their open compiler and formula obligations are outside this
session. The final theorem of the EPQ has not been fully formalised.
