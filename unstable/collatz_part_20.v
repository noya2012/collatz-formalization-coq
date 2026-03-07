Load "collatz_part_19_1.v".
Local Open Scope nat.

(* Macrostep preserves mod6=2 *)
Corollary canonical_mod62_macrostep_end_mod6 :
  forall m0,
    m0 mod 6 = 2 ->
    canonical_mod62_macrostep_end m0 mod 6 = 2.
Proof.
intros m0 Hm0_mod6.
pose proof (canonical_mod62_macrostep_spec m0 Hm0_mod6) as H.
set (chains := canonical_mod62_macrostep_chains m0) in H.
set (m2 := canonical_mod62_macrostep_end m0) in H.
destruct H as [_ [_ [Hm2 _]]].
subst m2.
exact Hm2.
Qed.

(* Odd number is 2*(q/2)+1 *)
Lemma odd_decomp_div2 :
  forall q,
    is_odd q ->
    q = 2 * (q / 2) + 1.
Proof.
intros q Hodd.
pose proof (Nat.div_mod q 2 ltac:(lia)) as Hdiv.
assert (Hmod : q mod 2 = 1).
{
assert (Hodd_bool : Nat.odd q = true).
{ unfold Nat.odd. unfold is_odd in Hodd. rewrite Hodd. reflexivity. }
apply Nat.odd_spec in Hodd_bool.
destruct Hodd_bool as [k Hk].
subst q.
rewrite Nat.add_mod by lia.
rewrite Nat.mul_mod by lia.
simpl.
reflexivity.
}
rewrite Hmod in Hdiv.
replace ((q / 2) * 2) with (2 * (q / 2)) in Hdiv by
(rewrite Nat.mul_comm; reflexivity).
exact Hdiv.
Qed.

(* Closed form for macrostep end value *)
Lemma canonical_mod62_macrostep_end_closed_form :
  forall m0,
    m0 mod 6 = 2 ->
    exists d0 n0 d1 q1 n1,
      factor2 m0 = (d0, n0) /\
      let m1 := n0 in
      factor2 (m1 + 1) = (d1, q1) /\
      n1 = q1 / 2 /\
      d1 >= 1 /\
      m1 = valid_R1R0_entry_number d1 n1 /\
      canonical_mod62_macrostep_end m0 =
        2 * 3 ^ d1 * n1 + (3 ^ d1 - 1).
Proof.
intros m0 Hm0_mod6.
unfold canonical_mod62_macrostep_end.
remember (factor2 m0) as p0 eqn:Hp0.
destruct p0 as [d0 n0].
remember (factor2 (n0 + 1)) as p1 eqn:Hp1.
destruct p1 as [d1 q1].
set (n1 := q1 / 2).
exists d0, n0, d1, q1, n1.
split.
{ reflexivity. }
cbv beta.
split.
{ symmetry. exact Hp1. }
split; [reflexivity|].
assert (Hm0_ge1 : m0 >= 1).
{
pose proof (Nat.div_mod m0 6 ltac:(lia)) as Hdiv.
rewrite Hm0_mod6 in Hdiv.
lia.
}
assert (Hq1_odd : is_odd q1).
{
pose proof (factor2_spec_odd (n0 + 1) ltac:(lia)) as H.
unfold factor2_odd in H.
rewrite <- Hp1 in H.
exact H.
}
assert (Hn0_odd : is_odd n0).
{
pose proof (factor2_spec_odd m0 Hm0_ge1) as H.
unfold factor2_odd in H.
rewrite <- Hp0 in H.
exact H.
}
assert (Hn0p1_even : is_even (n0 + 1)).
{
unfold is_even.
replace (n0 + 1) with (S n0) by lia.
rewrite Nat.even_succ.
unfold Nat.odd.
unfold is_odd in Hn0_odd.
rewrite Hn0_odd.
simpl.
reflexivity.
}
assert (Hd1_ge1 : d1 >= 1).
{
destruct d1 as [|d1'].
- pose proof (factor2_spec_decomp (n0 + 1)) as H.
unfold factor2_odd, factor2_exp in H.
rewrite <- Hp1 in H.
simpl in H.
unfold is_even in Hn0p1_even.
unfold is_odd in Hq1_odd.
rewrite H in Hn0p1_even.
rewrite Nat.mul_1_r in Hn0p1_even.
rewrite Hq1_odd in Hn0p1_even.
discriminate.
- lia.
}
split; [exact Hd1_ge1|].
assert (Hn0p1_decomp : (n0 + 1) = q1 * 2 ^ d1).
{
pose proof (factor2_spec_decomp (n0 + 1)) as H.
unfold factor2_odd, factor2_exp in H.
rewrite <- Hp1 in H.
exact H.
}
assert (Hn1_def : n1 = q1 / 2) by reflexivity.
assert (Hq1_form : q1 = 2 * n1 + 1).
{
pose proof (odd_decomp_div2 q1 Hq1_odd) as H.
rewrite <- Hn1_def in H.
exact H.
}
assert (Hn0_as_R1R0 : n0 = valid_R1R0_entry_number d1 n1).
{
apply (Nat.add_cancel_r _ _ 1).
rewrite valid_R1R0_entry_number_plus1.
rewrite Hn0p1_decomp.
rewrite (Nat.mul_comm q1 (2 ^ d1)).
rewrite Hq1_form.
reflexivity.
}
split; [exact Hn0_as_R1R0|].
rewrite Hn0_as_R1R0.
apply repeat_R1R0_output_closed_form_no_div; lia.
Qed.

(* Macrostep end > odd core *)
Lemma canonical_mod62_macrostep_end_gt_factor2_odd :
  forall m0,
    m0 mod 6 = 2 ->
    canonical_mod62_macrostep_end m0 > factor2_odd m0.
Proof.
intros m0 Hm0_mod6.
destruct (canonical_mod62_macrostep_end_closed_form m0 Hm0_mod6)
as (d0 & n0 & d1 & q1 & n1 & Hp0 & Hp1 & Hn1 & Hd1_ge1 & Hn0_as_entry & Hend).
unfold factor2_odd.
rewrite Hp0.
simpl.
rewrite Hend.
rewrite Hn0_as_entry.
unfold valid_R1R0_entry_number.
pose proof (pow3_gt_pow2 d1 Hd1_ge1) as Hpow.
set (A := 3 ^ d1).
set (B := 2 ^ d1).
set (k := 2 * n1 + 1).
assert (Hk_ge1 : 1 <= k) by (unfold k; lia).
assert (HB_ge1 : 1 <= B) by (subst B; apply pow2_ge1).
assert (HA_ge1 : 1 <= A) by (subst A; apply pow3_ge1).
assert (HL :
2 * A * n1 + (A - 1) = A * k - 1).
{
unfold k.
rewrite (Nat.add_sub_assoc (2 * A * n1) A 1) by lia.
replace (2 * A * n1 + A) with (A * (2 * n1 + 1)) by ring.
reflexivity.
}
assert (HR :
2 * B * n1 + (B - 1) = B * k - 1).
{
unfold k.
rewrite (Nat.add_sub_assoc (2 * B * n1) B 1) by lia.
replace (2 * B * n1 + B) with (B * (2 * n1 + 1)) by ring.
reflexivity.
}
rewrite HL.
rewrite HR.
assert (HBA : B + 1 <= A) by (subst A B; lia).
assert (Hmul : (B + 1) * k <= A * k) by (apply Nat.mul_le_mono_r; exact HBA).
replace ((B + 1) * k) with (B * k + k) in Hmul by ring.
assert (Hbk1 : B * k + 1 <= A * k) by (eapply Nat.le_trans; [|exact Hmul]; lia).
assert (HBk_le_Ak1 : B * k <= A * k - 1) by lia.
apply (Nat.lt_le_trans _ (B * k) _).
- assert (HBk_pos : 1 <= B * k).
{
assert (Hk_le : k <= B * k).
{
destruct B as [|B']; [lia|].
rewrite Nat.mul_succ_l.
lia.
}
eapply Nat.le_trans; [exact Hk_ge1|exact Hk_le].
}
lia.
- exact HBk_le_Ak1.
Qed.

(* Growth when d0=1 and d1>=2 *)
Lemma canonical_mod62_macrostep_end_gt_self_if_d0_eq1_d1_ge2 :
  forall m0 n0 d1 q1,
    m0 mod 6 = 2 ->
    factor2 m0 = (1, n0) ->
    factor2 (n0 + 1) = (d1, q1) ->
    d1 >= 2 ->
    canonical_mod62_macrostep_end m0 > m0.
Proof.
intros m0 n0 d1 q1 Hm0_mod6 Hfac0 Hfac1 Hd1_ge2.
unfold canonical_mod62_macrostep_end.
rewrite Hfac0.
simpl.
rewrite Hfac1.
simpl.
set (n1 := q1 / 2).
assert (Hq1_odd : is_odd q1).
{
pose proof (factor2_spec_odd (n0 + 1) ltac:(lia)) as Hodd.
unfold factor2_odd in Hodd.
rewrite Hfac1 in Hodd.
cbn [snd] in Hodd.
exact Hodd.
}
assert (Hq1_form : q1 = 2 * n1 + 1).
{
unfold n1.
pose proof (odd_decomp_div2 q1 Hq1_odd) as H.
exact H.
}
assert (Hn0_as_entry : n0 = valid_R1R0_entry_number d1 n1).
{
apply (Nat.add_cancel_r _ _ 1).
rewrite valid_R1R0_entry_number_plus1.
pose proof (factor2_spec_decomp (n0 + 1)) as Hdecomp1.
unfold factor2_odd, factor2_exp in Hdecomp1.
rewrite Hfac1 in Hdecomp1.
rewrite Hdecomp1.
rewrite Nat.mul_comm.
rewrite Hq1_form.
reflexivity.
}
pose proof (factor2_spec_decomp m0) as Hm0_decomp.
unfold factor2_odd, factor2_exp in Hm0_decomp.
rewrite Hfac0 in Hm0_decomp.
simpl in Hm0_decomp.
rewrite Hm0_decomp.
rewrite (Nat.mul_comm n0 2).
rewrite Hn0_as_entry.
rewrite (repeat_R1R0_output_closed_form_no_div d1 n1) by lia.
unfold valid_R1R0_entry_number.
set (k := 2 * n1 + 1).
assert (Hk_ge1 : 1 <= k) by (unfold k; lia).
assert (Hpow2_ge1 : 1 <= 2 ^ d1) by apply pow2_ge1.
assert (Hpow3_ge1 : 1 <= 3 ^ d1) by apply pow3_ge1.
assert (HL : 2 * 3 ^ d1 * n1 + (3 ^ d1 - 1) = 3 ^ d1 * k - 1).
{
unfold k.
replace (3 ^ d1 * (2 * n1 + 1)) with (2 * 3 ^ d1 * n1 + 3 ^ d1) by ring.
apply Nat.add_sub_assoc.
exact Hpow3_ge1.
}
assert (HR : 2 * (2 * 2 ^ d1 * n1 + (2 ^ d1 - 1)) = 2 ^ (S d1) * k - 2).
{
unfold k.
rewrite Nat.mul_add_distr_l.
rewrite Nat.mul_assoc.
replace (2 * (2 * 2 ^ d1 * n1)) with (2 ^ (S d1) * (2 * n1)) by
(rewrite Nat.pow_succ_r by lia; ring).
assert (Hsub : 2 * (2 ^ d1 - 1) = 2 * 2 ^ d1 - 2).
{
replace 2 with (2 * 1) by lia.
rewrite Nat.mul_sub_distr_l by (apply pow2_ge1).
simpl.
lia.
}
rewrite Hsub.
replace (2 * 2 ^ d1) with (2 ^ (S d1)) by
(rewrite Nat.pow_succ_r by lia; ring).
replace (2 * 2 ^ (S d1) * n1) with (2 ^ (S d1) * (2 * n1)) by ring.
assert (Hpow2_ge2 : 2 <= 2 ^ (S d1)).
{
pose proof (pow2_ge_4_if_ge2 (S d1) ltac:(lia)) as H4.
lia.
}
rewrite Nat.add_sub_assoc by exact Hpow2_ge2.
replace (2 ^ (S d1) * (2 * n1) + 2 ^ (S d1)) with (2 ^ (S d1) * (2 * n1 + 1)) by ring.
reflexivity.
}
rewrite HL.
rewrite HR.
pose proof (pow3_ge_pow2_succ_from2 d1 Hd1_ge2) as Hpow_ge.
assert (Hmul_ge : 2 ^ (S d1) * k <= 3 ^ d1 * k).
{ apply Nat.mul_le_mono_r; exact Hpow_ge. }
set (A := 3 ^ d1 * k).
set (B := 2 ^ (S d1) * k).
assert (HB_ge2 : 2 <= B).
{
assert (Hpow2_ge2 : 2 <= 2 ^ (S d1)).
{
pose proof (pow2_ge_4_if_ge2 (S d1) ltac:(lia)) as H4.
lia.
}
assert (Hpow2_le_B : 2 ^ (S d1) <= B).
{
unfold B.
destruct k as [|k']; [lia|].
simpl.
rewrite Nat.mul_succ_r.
lia.
}
eapply Nat.le_trans; [exact Hpow2_ge2|exact Hpow2_le_B].
}
assert (HBm2_lt_HBm1 : B - 2 < B - 1).
{
destruct B as [|B']; [lia|].
destruct B' as [|B'']; [lia|].
simpl.
lia.
}
assert (HB_le_HA : B <= A).
{ unfold A, B. exact Hmul_ge. }
assert (HBm1_le_HAm1 : B - 1 <= A - 1).
{ apply Nat.sub_le_mono_r; exact HB_le_HA. }
apply (Nat.lt_le_trans _ (B - 1) _).
- exact HBm2_lt_HBm1.
- eapply Nat.le_trans; [exact HBm1_le_HAm1|].
unfold A.
lia.
Qed.

(* Macrostep end at 8 equals 2 *)
Lemma canonical_mod62_macrostep_end_8 :
  canonical_mod62_macrostep_end 8 = 2.
Proof.
vm_compute.
reflexivity.
Qed.
(* Cycle condition: mod6=2 and returns to start *)
Definition canonical_mod62_cycle (t m0 : nat) : Prop :=
  t >= 1 /\
  m0 mod 6 = 2 /\
  canonical_mod62_iterated_end t m0 = m0.

(* Nontrivial cycle excludes 2 *)
Definition canonical_mod62_nontrivial_cycle (t m0 : nat) : Prop :=
  canonical_mod62_cycle t m0 /\ m0 <> 2.

(* Macrostep end at 2 equals 2 *)
Lemma canonical_mod62_macrostep_end_2 :
  canonical_mod62_macrostep_end 2 = 2.
Proof.
unfold canonical_mod62_macrostep_end.
simpl.
reflexivity.
Qed.

(* Iterated macrostep at 2 always returns 2 *)
Lemma canonical_mod62_iterated_end_2 :
  forall t, canonical_mod62_iterated_end t 2 = 2.
Proof.
induction t as [|t IH].
- reflexivity.
- simpl.
rewrite canonical_mod62_macrostep_end_2.
exact IH.
Qed.

(* 2 is a cycle for any t>=1 *)
Corollary canonical_mod62_cycle_at_2 :
  forall t, t >= 1 -> canonical_mod62_cycle t 2.
Proof.
intros t Ht.
unfold canonical_mod62_cycle.
split.
- exact Ht.
- split.
+ simpl. reflexivity.
+ apply canonical_mod62_iterated_end_2.
Qed.