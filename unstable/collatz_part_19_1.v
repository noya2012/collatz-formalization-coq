Load "collatz_part_19.v".

Local Open Scope nat.

(* Odd numbers are at least 1 *)
Lemma is_odd_ge1 : forall n,
  is_odd n ->
  n >= 1.
Proof.
intros n Hodd.
destruct n as [|n].
- unfold is_odd in Hodd. simpl in Hodd. discriminate.
- lia.
Qed.

(* Fixed point implies collatz equation *)
Lemma fixed_point_implies_collatz_eq :
  forall d0 n0 d1 q1 n1,
    factor2 (n0 + 1) = (d1, q1) ->
    n1 = q1 / 2 ->
    d1 >= 1 ->
    n0 * 2 ^ d0 = 2 * 3 ^ d1 * n1 + (3 ^ d1 - 1) ->
    let k := q1 in
    k >= 1 /\ 3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0.
Proof.
intros d0 n0 d1 q1 n1 Hfac Hn1 _ Hfix.
cbn.
assert (Hn0p1_ge1 : n0 + 1 >= 1) by lia.
assert (Hq1_odd : is_odd q1).
{
pose proof (factor2_spec_odd (n0 + 1) Hn0p1_ge1) as Hodd.
unfold factor2_odd in Hodd.
rewrite Hfac in Hodd.
simpl in Hodd.
exact Hodd.
}
assert (Hq1_ge1 : q1 >= 1) by (apply is_odd_ge1; exact Hq1_odd).
assert (Hn0p1 : n0 + 1 = 2 ^ d1 * q1).
{
pose proof (factor2_spec_decomp (n0 + 1)) as Hdecomp.
unfold factor2_odd, factor2_exp in Hdecomp.
rewrite Hfac in Hdecomp.
simpl in Hdecomp.
rewrite Nat.mul_comm in Hdecomp.
exact Hdecomp.
}
destruct (odd_decomposition q1 Hq1_odd) as [k Hq1_as].
assert (Hq1_div2 : q1 / 2 = k).
{
rewrite Hq1_as.
replace (2 * k + 1) with (k * 2 + 1) by lia.
assert (H2 : 2 <> 0) by lia.
rewrite (Nat.div_add_l k 2 1 H2).
simpl.
rewrite Nat.add_0_r.
reflexivity.
}
assert (Hn1k : n1 = k).
{ rewrite Hn1. rewrite Hq1_div2. reflexivity. }
assert (Hpow3_ge1 : 1 <= 3 ^ d1) by apply pow3_ge1.
assert (Hmain : n0 * 2 ^ d0 + 1 = 3 ^ d1 * q1).
{
rewrite Hfix.
rewrite <- Nat.add_assoc.
replace ((3 ^ d1 - 1) + 1) with (3 ^ d1) by (symmetry; apply Nat.sub_add; exact Hpow3_ge1).
rewrite Hn1k.
rewrite Hq1_as.
ring.
}
split; [exact Hq1_ge1|].
assert (Hpos3 : 1 <= 3 ^ d1 * q1).
{
replace 1 with (1 * 1) by lia.
apply Nat.mul_le_mono.
- exact Hpow3_ge1.
- exact Hq1_ge1.
}
assert (Hlhs : 3 ^ d1 * q1 - 1 = n0 * 2 ^ d0).
{
apply (Nat.add_cancel_r _ _ 1).
replace (3 ^ d1 * q1 - 1 + 1) with (3 ^ d1 * q1) by (symmetry; apply Nat.sub_add; exact Hpos3).
rewrite Hmain.
reflexivity.
}
assert (Hn0_eq : n0 = 2 ^ d1 * q1 - 1).
{
apply (Nat.add_cancel_r _ _ 1).
assert (Hpos2 : 1 <= 2 ^ d1 * q1) by (rewrite <- Hn0p1; lia).
rewrite (Nat.sub_add 1 (2 ^ d1 * q1) Hpos2).
exact Hn0p1.
}
rewrite Hlhs.
rewrite Hn0_eq.
reflexivity.
Qed.

(* Power of 2 is at least 1 *)
Lemma pow2_ge1 : forall d, 1 <= 2 ^ d.
Proof.
induction d; simpl; lia.
Qed.

(* 2^d >= 4 when d >= 2 *)
Lemma pow2_ge_4_if_ge2 : forall d, d >= 2 -> 2 ^ d >= 4.
Proof.
intros d Hd.
replace 4 with (2 ^ 2) by reflexivity.
apply Nat.pow_le_mono_r; lia.
Qed.

(* 3^n >= 2^(n+1) for n >= 2 *)
Lemma pow3_ge_pow2_succ_from2 :
  forall n, n >= 2 -> 3 ^ n >= 2 ^ (S n).
Proof.
intros n Hn.
assert (exists k, n = 2 + k) as [k Hk] by (exists (n - 2); lia).
subst n.
induction k as [|k IHk].
- simpl. lia.
- pose proof (IHk ltac:(lia)) as IH.
rewrite Nat.add_succ_r.
rewrite Nat.pow_succ_r by lia.
rewrite Nat.pow_succ_r by lia.
assert (IH' : 2 ^ S (2 + k) <= 3 ^ (2 + k)) by exact IH.
assert (Hmul : 2 ^ S (2 + k) * 2 <= 3 ^ (2 + k) * 2) by nia.
replace (2 ^ S (2 + k) * 2) with (2 * 2 ^ S (2 + k)) in Hmul by
(rewrite Nat.mul_comm; reflexivity).
replace (3 ^ (2 + k) * 2) with (2 * 3 ^ (2 + k)) in Hmul by
(rewrite Nat.mul_comm; reflexivity).
assert (H32' : 3 ^ (2 + k) * 2 <= 3 ^ (2 + k) * 3) by nia.
replace (3 ^ (2 + k) * 2) with (2 * 3 ^ (2 + k)) in H32' by
(rewrite Nat.mul_comm; reflexivity).
replace (3 ^ (2 + k) * 3) with (3 * 3 ^ (2 + k)) in H32' by
(rewrite Nat.mul_comm; reflexivity).
eapply Nat.le_trans; [exact Hmul|].
exact H32'.
Qed.

(* 3^d > 2^d for d >= 1 *)
Lemma pow3_gt_pow2 : forall d, d >= 1 -> 3 ^ d > 2 ^ d.
Proof.
intros d Hd.
destruct d as [|d']; [lia|].
destruct d' as [|d''].
- simpl. lia.
- assert (Hge : 3 ^ (S (S d'')) >= 2 ^ (S (S (S d'')))) by
(apply pow3_ge_pow2_succ_from2; lia).
rewrite (Nat.pow_succ_r 2 (S (S d''))) in Hge by lia.
assert (Hpos : 1 <= 2 ^ (S (S d''))) by apply pow2_ge1.
assert (Hlt : 2 ^ (S (S d'')) < 2 ^ (S (S d'')) * 2) by nia.
rewrite Nat.mul_comm in Hge.
assert (Hge' : 2 ^ (S (S d'')) * 2 <= 3 ^ (S (S d''))) by exact Hge.
eapply Nat.lt_le_trans; [exact Hlt|exact Hge'].
Qed.

(* Helper lemma for main theorem *)
Lemma collatz_eq_implies_eq :
  forall d0 n0 d1 q1 n1,
    factor2 (n0 + 1) = (d1, q1) ->
    n1 = q1 / 2 ->
    d1 >= 1 ->
    n0 * 2 ^ d0 = 2 * 3 ^ d1 * n1 + (3 ^ d1 - 1) ->
    let k := q1 in
    k >= 1 /\ 3 ^ d1 * k - 1 = (2 ^ d1 * k - 1) * 2 ^ d0.
Proof.
intros d0 n0 d1 q1 n1 Hfac Hn1 Hd1 Hfix.
exact (fixed_point_implies_collatz_eq d0 n0 d1 q1 n1 Hfac Hn1 Hd1 Hfix).
Qed.