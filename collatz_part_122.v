(* Compatible with Coq 8.10.2: *)
Load "collatz_part_121.v".

(* Strict monotonicity theorem: repeat_R0 output is strictly increasing with respect to n *)
Theorem repeat_R0_output_strict_mono : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 -> n < n' ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) <
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
rewrite (repeat_R0_output_reaches_one D n HD Hn).
rewrite (repeat_R0_output_reaches_one D n' HD Hn').
exact Hlt.
Qed.

(* Injectivity: for fixed D, equal outputs imply equal n *)
Corollary repeat_R0_output_injective_in_n : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) =
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
rewrite (repeat_R0_output_reaches_one D n HD Hn) in Heq.
rewrite (repeat_R0_output_reaches_one D n' HD Hn') in Heq.
exact Heq.
Qed.

(* =============== Incremental (difference) form auxiliary theorems =============== *)
(* Single-step difference: since the final value of R0R0 pattern is n itself, single-step difference equals the difference in n *)
Lemma repeat_R0_output_step_delta : forall D n,
  D >= 1 -> n >= 1 ->
  sequence_end (valid_R0R0_entry_number D (S n)) (repeat_R0 D)
    = sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) + 1.
Proof.
intros D n HD Hn.
rewrite (repeat_R0_output_reaches_one D (S n) HD).
2:{ lia. }
rewrite (repeat_R0_output_reaches_one D n HD Hn).
simpl.
lia.
Qed.

(* Generalized difference: for all n <= n', output difference = n' - n *)
Lemma repeat_R0_output_linear_increment : forall D n n',
  D >= 1 -> n >= 1 -> n' >= n ->
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D)
    = sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D)
      + (n' - n).
Proof.
intros D n n' HD Hn Hle.
rewrite (repeat_R0_output_reaches_one D n' HD).
2:{ lia. }
rewrite (repeat_R0_output_reaches_one D n HD Hn).
replace n' with (n + (n' - n)) at 1 by lia.
lia.
Qed.

(* Single-step strict increase as a corollary of difference *)
Corollary repeat_R0_output_step_strict_increase : forall D n,
  D >= 1 -> n >= 1 ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) <
  sequence_end (valid_R0R0_entry_number D (S n)) (repeat_R0 D).
Proof.
intros D n HD Hn.
rewrite (repeat_R0_output_step_delta D n HD Hn).
assert (1 > 0) by lia.
lia.
Qed.

(* Fast strict monotonicity from difference form - equivalent to the proven strict_mono *)
Corollary repeat_R0_output_strict_mono_alt : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 -> n < n' ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) <
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
assert (Hle: n' >= n) by lia.
rewrite (repeat_R0_output_linear_increment D n n' HD Hn Hle).
assert ((n' - n) > 0).
{ apply sub_pos_strict; lia. }
lia.
Qed.

(* Injectivity can also be given directly from difference form (alternative to previous proof) *)
Corollary repeat_R0_output_injective_in_n_alt : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) =
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
destruct (Nat.lt_trichotomy n n') as [Hlt|[Heq'|Hgt]]; try lia.
-
pose proof (repeat_R0_output_strict_mono_alt D n n' HD Hn Hn' Hlt) as HltOut.
rewrite Heq in HltOut; lia.
-
pose proof (repeat_R0_output_strict_mono_alt D n' n HD Hn' Hn Hgt) as HltOut.
rewrite <- Heq in HltOut; lia.
Qed.