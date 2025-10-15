Load "collatz_part_7.v".


(* Valid input and parity in R1R0 pattern *)
Lemma R1R0_two_steps_reduce : forall d n,
  d >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number d n in
  (3 * m + 1) = 2 * valid_R1R0_entry_number (d - 1) (3 * n + 1).
Proof.
intros d n Hd Hn m.
unfold m, valid_R1R0_entry_number.
destruct d as [|d'].
-
lia.
-
assert (H_pow: 2^(S d') = 2 * 2^d').
{
apply Nat.pow_succ_r.
lia.
}
repeat rewrite H_pow.
assert (H_sub_pos: 2 * 2^d' >= 1).
{
assert (H_ge_1: 2^d' > 0).
{
apply gt_0_2_pow.
}
lia.
}
assert (H_pow_ge_1: 2^d' >= 1).
{
assert (H_gt_0: 2^d' > 0) by apply gt_0_2_pow.
lia.
}
simpl.
assert (H_d_eq: d' - 0 = d').
{
lia.
}
repeat rewrite H_d_eq.
repeat rewrite Nat.add_0_r.
lia.
Qed.

(* Lemma for sequence end value connection calculation - combined with R1R0_two_steps_reduce to derive R1R0_pattern_closure *)
Lemma sequence_end_two_steps : forall n,
  valid_input n ->
  is_odd n ->
  sequence_end n [R1; R0] = (3 * n + 1) / 2.
Proof.
intros n Hvalid Hodd.
unfold sequence_end.
simpl.
unfold nth_sequence_value.
simpl.
unfold collatz_step.
unfold is_odd in Hodd.
rewrite Hodd.
simpl.
unfold collatz_step.
assert (H_expr_eq: n + (n + (n + 0)) + 1 = 3 * n + 1).
{
ring.
}
assert (H_even: Nat.even (3 * n + 1) = true).
{
apply even_3n_plus_1.
unfold is_odd.
exact Hodd.
}
rewrite <- H_expr_eq in H_even.
rewrite H_even.
rewrite H_expr_eq.
reflexivity.
Qed.

 (* R1R0 pattern closure *)
Lemma R1R0_pattern_closure : forall d n,
  d >= 1 -> n >= 0 ->
  let m := valid_R1R0_entry_number d n in
  sequence_end m [R1; R0] = valid_R1R0_entry_number (d-1) (3*n+1).
Proof.
intros d n Hd Hn m.
unfold m.
assert (Hprops: valid_input (valid_R1R0_entry_number d n) /\ is_odd (valid_R1R0_entry_number d n)).
{
apply valid_R1R0_entry_number_properties; auto.
}
destruct Hprops as [Hvalid_m Hodd_m].
assert (H_seq_end: sequence_end (valid_R1R0_entry_number d n) [R1; R0] =
(3 * valid_R1R0_entry_number d n + 1) / 2).
{
apply sequence_end_two_steps; auto.
}
assert (H_reduce: (3 * valid_R1R0_entry_number d n + 1) =
2 * valid_R1R0_entry_number (d - 1) (3 * n + 1)).
{
apply R1R0_two_steps_reduce; auto.
}
rewrite H_seq_end.
rewrite H_reduce.
assert (H_div: (2 * valid_R1R0_entry_number (d - 1) (3 * n + 1)) / 2 =
valid_R1R0_entry_number (d - 1) (3 * n + 1)).
{
rewrite Nat.mul_comm.
apply Nat.div_mul.
assert (H_ge_1: valid_R1R0_entry_number (d - 1) (3 * n + 1) >= 1).
{
destruct d as [|d'].
-
lia.
-
simpl.
destruct d' as [|d''].
+
simpl.
unfold valid_R1R0_entry_number.
simpl.
assert (H_3n_ge_1: 3 * n + 1 >= 1).
{
lia.
}
lia.
+
unfold valid_R1R0_entry_number.
assert (H_pow_pos: 2^(S d'') > 0).
{
apply gt_0_2_pow.
}
assert (H_pow_ge_1: 2^(S d'') >= 1).
{
lia.
}
assert (H_3n_ge_1: 3 * n + 1 >= 1).
{
lia.
}
assert (H_sub_simp: S d'' - 0 = S d'').
{
lia.
}
rewrite H_sub_simp.
assert (H_first_part: 2 * 2^(S d'') * (3 * n + 1) >= 2).
{
assert (H_step1: 2 * 2^(S d'') >= 2).
{
assert (H_eq: 2 * 1 = 2) by reflexivity.
rewrite <- H_eq.
apply Nat.mul_le_mono_l.
exact H_pow_ge_1.
}
assert (H_step2: 2 * 2^(S d'') * (3 * n + 1) >= 2 * 2^(S d'') * 1).
{
apply Nat.mul_le_mono_l.
exact H_3n_ge_1.
}
assert (H_simp: 2 * 2^(S d'') * 1 = 2 * 2^(S d'')) by ring.
rewrite H_simp in H_step2.
apply (Nat.le_trans 2 (2 * 2^(S d''))).
- exact H_step1.
- exact H_step2.
}
assert (H_second_part: 2^(S d'') - 1 >= 0).
{
lia.
}
assert (H_total: 2 * 2^(S d'') * (3 * n + 1) + (2^(S d'') - 1) >= 1).
{
apply (Nat.le_trans 1 2).
- lia.
- apply (Nat.le_trans 2 (2 * 2^(S d'') * (3 * n + 1))).
+ exact H_first_part.
+ apply Nat.le_add_r.
}
exact H_total.
}
lia.
}
rewrite H_div.
reflexivity.
Qed.