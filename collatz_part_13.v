Load "collatz_part_12.v".

(* If n >= 1, then 2^n is even *)
Lemma power_2_even_property : forall n : nat, n >= 1 -> Nat.even (2^n) = true.
Proof.
intros n Hn.
induction n as [|n IH].
- lia.
- rewrite Nat.pow_succ_r by lia.
rewrite Nat.mul_comm.
rewrite Nat.even_mul.
simpl.
rewrite Bool.orb_true_r.
reflexivity.
Qed.

(* If d1 ≤ d2, then cancel left 2^d1 to get o1 = 2^(d2-d1) * o2 *)
Lemma pow_cancel_lower : forall d1 d2 o1 o2,
  d1 <= d2 ->
  2 ^ d1 * o1 = 2 ^ d2 * o2 ->
  o1 = 2 ^ (d2 - d1) * o2.
Proof.
intros d1 d2 o1 o2 Hle Heq.
replace d2 with (d1 + (d2 - d1)) in Heq by lia.
rewrite Nat.pow_add_r in Heq by lia.
rewrite <- Nat.mul_assoc in Heq.
apply Nat.mul_cancel_l in Heq; [| apply (Nat.pow_nonzero 2 d1); discriminate].
assumption.
Qed.

(* If d1 ≤ d2 and o1,o2 are odd, then 2^d1*o1 = 2^d2*o2 implies d1=d2 and o1=o2 *)
Lemma pow2_times_odd_unique_le : forall d1 d2 o1 o2,
  d1 <= d2 -> d1 >= 1 -> d2 >= 1 ->
  Nat.even o1 = false -> Nat.even o2 = false ->
  2 ^ d1 * o1 = 2 ^ d2 * o2 ->
  d1 = d2 /\ o1 = o2.
Proof.
intros d1 d2 o1 o2 Hle Hd1 Hd2 Ho1 Ho2 Heq.
destruct (Nat.eq_dec d1 d2) as [Heqdd|Hneq].
- subst d2.
assert (Hnz: 2 ^ d1 <> 0) by (apply (Nat.pow_nonzero 2 d1); discriminate).
apply Nat.mul_cancel_l in Heq; [|assumption].
split; [reflexivity | assumption].
- assert (Hlt: d1 < d2) by lia.
set (delta := d2 - d1).
assert (Hdelta: delta >= 1) by (unfold delta; lia).
apply pow_cancel_lower in Heq; auto.
rewrite Heq in Ho1.
rewrite Nat.even_mul in Ho1.
assert (E': Nat.even (2 ^ (d2 - d1)) = true) by (apply power_2_even_property; unfold delta; lia).
rewrite E' in Ho1.
rewrite Ho2 in Ho1.
simpl in Ho1.
discriminate Ho1.
Qed.

(* Unique decomposition of 2^d * odd number (order of d1,d2 not required) *)
Lemma pow2_times_odd_unique : forall d1 d2 o1 o2,
  d1 >= 1 -> d2 >= 1 ->
  Nat.even o1 = false -> Nat.even o2 = false ->
  2 ^ d1 * o1 = 2 ^ d2 * o2 ->
  d1 = d2 /\ o1 = o2.
Proof.
intros d1 d2 o1 o2 Hd1 Hd2 Ho1 Ho2 Heq.
destruct (le_ge_dec d1 d2) as [Hle|Hge].
- apply pow2_times_odd_unique_le; auto.
-
destruct (pow2_times_odd_unique_le d2 d1 o2 o1 Hge Hd2 Hd1 Ho2 Ho1 (eq_sym Heq)) as [Hd Ho].
subst; split; auto.
Qed.

(* valid_R1R0_entry_number d n plus 1 can be expressed as 2^d*(2*n+1) *)
Lemma valid_R1R0_entry_number_plus1 :
  forall d n, valid_R1R0_entry_number d n + 1 = 2 ^ d * (2 * n + 1).
Proof.
intros d n; unfold valid_R1R0_entry_number.
induction d as [|d IH].
- simpl. lia.
-
rewrite Nat.pow_succ_r by lia.
replace (2 * (2 * 2 ^ d) * n) with ((2 * 2 ^ d) * (2 * n)) by lia.
replace ((2 * 2 ^ d - 1) + 1) with (2 * 2 ^ d) by lia.
rewrite Nat.mul_add_distr_l.
lia.
Qed.

(* R1R0 Uniqueness Decomposition *)
Lemma R1R0_decomposition_unique : forall m d1 d2 n1 n2,
  is_odd m ->
  d1 >= 1 -> d2 >= 1 -> n1 >= 0 -> n2 >= 0 ->
  m = valid_R1R0_entry_number d1 n1 ->
  m = valid_R1R0_entry_number d2 n2 ->
  d1 = d2 /\ n1 = n2.
Proof.
intros m d1 d2 n1 n2 Hodd Hd1 Hd2 Hn1 Hn2 Hm1 Hm2.
unfold valid_R1R0_entry_number in Hm1, Hm2.
assert (H1: m + 1 = 2 ^ d1 * (2 * n1 + 1)) by (rewrite Hm1; apply valid_R1R0_entry_number_plus1).
assert (H2: m + 1 = 2 ^ d2 * (2 * n2 + 1)) by (rewrite Hm2; apply valid_R1R0_entry_number_plus1).
assert (E: 2 ^ d1 * (2 * n1 + 1) = 2 ^ d2 * (2 * n2 + 1)).
{ rewrite <- H1. rewrite H2. reflexivity. }
assert (O1: Nat.even (2 * n1 + 1) = false).
{ rewrite Nat.even_add. rewrite Nat.even_mul. simpl. reflexivity. }
assert (O2: Nat.even (2 * n2 + 1) = false).
{ rewrite Nat.even_add. rewrite Nat.even_mul. simpl. reflexivity. }
destruct (pow2_times_odd_unique d1 d2 (2 * n1 + 1) (2 * n2 + 1) Hd1 Hd2 O1 O2 E) as [Hd Ho].
simpl in Ho.
lia.
Qed.

  (* R0R0 Uniqueness Decomposition *)
  Lemma R0R0_decomposition_unique :
    forall m d1 d2 n1 n2,
      m = valid_R0R0_entry_number d1 n1 ->
      m = valid_R0R0_entry_number d2 n2 ->
      is_odd n1 ->
      is_odd n2 ->
      d1 = d2 /\ n1 = n2.
  Proof.
intros m d1 d2 n1 n2 Hm1 Hm2 Ho1 Ho2.
unfold valid_R0R0_entry_number in Hm1, Hm2.
rewrite Nat.mul_comm in Hm1.
rewrite Nat.mul_comm in Hm2.
set (E := eq_trans (eq_sym Hm1) Hm2).
destruct (Nat.eq_dec d1 d2) as [Heq|Hneq].
{ subst d2. split; [reflexivity|].
apply Nat.mul_cancel_l in E; [assumption| apply Nat.pow_nonzero; discriminate]. }
destruct (Nat.lt_trichotomy d1 d2) as [Hlt|[Heq|Hgt]].
-
assert (Hle: d1 <= d2) by lia.
pose proof (pow_cancel_lower d1 d2 n1 n2 Hle E) as Hform.
assert (Nat.even n1 = true) as Contra.
{ rewrite Hform.
rewrite Nat.even_mul.
assert (Nat.even (2 ^ (d2 - d1)) = true) by (apply power_2_even_property; lia).
rewrite H. simpl. reflexivity. }
unfold is_odd in Ho1. rewrite Ho1 in Contra. discriminate.
-
contradiction.
-
assert (Hlt': d2 < d1) by lia.
assert (Hle': d2 <= d1) by lia.
assert (E': 2 ^ d2 * n2 = 2 ^ d1 * n1) by (symmetry; exact E).
pose proof (pow_cancel_lower d2 d1 n2 n1 Hle' E') as Hform.
assert (Nat.even n2 = true) as Contra.
{ rewrite Hform.
rewrite Nat.even_mul.
assert (Nat.even (2 ^ (d1 - d2)) = true) by (apply power_2_even_property; lia).
rewrite H. simpl. reflexivity. }
unfold is_odd in Ho2. rewrite Ho2 in Contra. discriminate.
Qed.