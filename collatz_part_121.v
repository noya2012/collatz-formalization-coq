(* Compatible with Coq 8.10.2: *)
Load "collatz_part_12.v".

(* Strict monotonicity theorem: repeat_R1R0 output is strictly increasing with respect to n *)
Theorem repeat_R1R0_output_strict_mono : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 -> n < n' ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
rewrite (repeat_R1R0_output_closed_form_no_div D n' HD Hn').
assert (Hpow_pos: 0 < 3 ^ D) by apply pow3_pos.
assert (Hfac_pos: 0 < 2 * 3 ^ D) by (apply mul_pos_pos_nat; lia || apply pow3_pos).
assert (Hdelta: n' - n > 0) by (apply sub_pos_strict; lia).
replace n' with (n + (n' - n)) at 2 by lia.
replace (2 * 3 ^ D * (n + (n' - n))) with
(2 * 3 ^ D * n + 2 * 3 ^ D * (n' - n)) by (rewrite Nat.mul_add_distr_l; lia).
assert (Htail: 0 < 2 * 3 ^ D * (n' - n)).
{ apply mul_pos_pos_nat.
- apply mul_pos_pos_nat; [lia|apply pow3_pos].
- apply sub_pos_strict; lia.
}
lia.
Qed.

(* Injectivity: for fixed D, equal outputs imply equal n *)
Corollary repeat_R1R0_output_injective_in_n : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) =
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
destruct (Nat.lt_trichotomy n n') as [Hlt | [Heq' | Hgt]].
- pose proof (repeat_R1R0_output_strict_mono D n n' HD Hn Hn' Hlt) as Hmono.
rewrite Heq in Hmono. lia.
- exact Heq'.
- pose proof (repeat_R1R0_output_strict_mono D n' n HD Hn' Hn Hgt) as Hmono.
rewrite <- Heq in Hmono. lia.
Qed.

(* =============== Incremental (difference) form auxiliary theorems =============== *)
(* Single-step closed-form difference: linear increment step size for n is constant 2 * 3^D *)
Lemma repeat_R1R0_output_step_delta : forall D n,
  D >= 1 -> n >= 0 ->
  sequence_end (valid_R1R0_entry_number D (S n)) (repeat_R1R0 D)
    = sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) + 2 * 3 ^ D.
Proof.
intros D n HD Hn.
rewrite (repeat_R1R0_output_closed_form_no_div D (S n) HD).
2:{ lia. }
rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
simpl.
replace (2 * 3 ^ D * S n) with (2 * 3 ^ D * n + 2 * 3 ^ D) by lia.
lia.
Qed.

(* Generalized difference: for all n <= n', output difference = 2 * 3^D * (n' - n) *)
Lemma repeat_R1R0_output_linear_increment : forall D n n',
  D >= 1 -> n >= 0 -> n' >= n ->
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D)
    = sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D)
      + 2 * 3 ^ D * (n' - n).
Proof.
intros D n n' HD Hn Hle.
rewrite (repeat_R1R0_output_closed_form_no_div D n' HD).
2:{ lia. }
rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
replace n' with (n + (n' - n)) at 1 by lia.
rewrite Nat.mul_add_distr_l.
lia.
Qed.

(* Single-step strict increase as a corollary of difference (avoids re-expanding closed form) *)
Corollary repeat_R1R0_output_step_strict_increase : forall D n,
  D >= 1 -> n >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <
  sequence_end (valid_R1R0_entry_number D (S n)) (repeat_R1R0 D).
Proof.
intros D n HD Hn.
rewrite (repeat_R1R0_output_step_delta D n HD Hn).
assert (2 * 3 ^ D > 0) by (apply mul_pos_pos_nat; lia || apply pow3_pos).
lia.
Qed.

(* Fast strict monotonicity from difference form - equivalent to the proven strict_mono *)
Corollary repeat_R1R0_output_strict_mono_alt : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 -> n < n' ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
assert (Hle: n' >= n) by lia.
rewrite (repeat_R1R0_output_linear_increment D n n' HD Hn Hle).
assert (2 * 3 ^ D * (n' - n) > 0).
{ apply mul_pos_pos_nat.
- apply mul_pos_pos_nat; lia || apply pow3_pos.
- apply sub_pos_strict; lia.
}
lia.
Qed.

(* Injectivity can also be given directly from difference form (alternative to previous proof) *)
Corollary repeat_R1R0_output_injective_in_n_alt : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) =
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
destruct (Nat.lt_trichotomy n n') as [Hlt|[Heq'|Hgt]]; try lia.
-
pose proof (repeat_R1R0_output_strict_mono_alt D n n' HD Hn Hn' Hlt) as HltOut.
rewrite Heq in HltOut; lia.
-
pose proof (repeat_R1R0_output_strict_mono_alt D n' n HD Hn' Hn Hgt) as HltOut.
rewrite <- Heq in HltOut; lia.
Qed.