Load "collatz_part_18.v".

(* build_k_steps decomposition: k1 steps followed by k2 steps equals building from intermediate state *)
Lemma build_k_steps_add : forall n k1 k2,
  build_k_steps n (k1 + k2) =
    build_k_steps n k1 ++
    build_k_steps (sequence_end n (build_k_steps n k1)) k2.
Proof.
intros n k1 k2.
induction k2 as [|k2 IH].
- simpl. rewrite Nat.add_0_r. rewrite app_nil_r. reflexivity.
-
rewrite Nat.add_succ_r.
simpl (build_k_steps n (S (k1 + k2))).
rewrite IH.
set (ops1 := build_k_steps n k1).
set (n1 := sequence_end n ops1).
set (ops2 := build_k_steps n1 k2).
change (build_k_steps n k1) with ops1.
change (sequence_end n (build_k_steps n k1)) with n1.
change (build_k_steps n1 k2) with ops2.
assert (Hend : sequence_end n (ops1 ++ ops2) = sequence_end n1 ops2).
{ subst n1 ops1 ops2. rewrite sequence_end_app. reflexivity. }
rewrite Hend.
simpl (build_k_steps n1 (S k2)).
fold ops2.
destruct (Nat.even (sequence_end n1 ops2)) eqn:He.
+ repeat rewrite app_assoc. reflexivity.
+ repeat rewrite app_assoc. reflexivity.
Qed.

(* Canonical conversion to mod6=2 orbit using build_k_steps as canonical prefix *)
Theorem direct_conversion_to_mod6_2_orbit_canonical :
  forall m,
    valid_input m ->
    exists (K k : nat) (m_final : nat) (ops : list CollatzOp),
      ops = build_k_steps m K /\
      length ops = k /\
      valid_sequence ops m /\
      sequence_end m ops = m_final /\
      m_final mod 6 = 2 /\
      k <= 2 * (log2 m + 1).
  Proof.
intros m Hvalid.
destruct (build_k_steps_numeric_canonical m Hvalid) as
[[d [n [Hd [Hn [Hm_entry [Hbuild Hseq_end]]]]]] |
[d [n [Hd [Hn [Hodd_n [Hm_entry [Hbuild [Hseq_end Hodd_m]]]]]]]]].
- exists d, (2 * d), (sequence_end m (repeat_R1R0 d)), (repeat_R1R0 d).
split.
+
symmetry; exact Hbuild.
+ split.
*
apply repeat_R1R0_length.
* split.
--
rewrite <- Hbuild. apply build_k_steps_valid; assumption.
-- split.
++
reflexivity.
++ split.
**
rewrite Hm_entry. apply R1R0_output_mod6; assumption.
**
assert (Hd_le_log2m1 : d <= log2 (m + 1)).
{ apply (R1R0_entry_d_log2_bound m d n); try assumption. }
assert (Hlog2_bound : log2 (m + 1) <= log2 m + 1).
{
assert (Hm_ge1 : m >= 1) by (unfold valid_input in Hvalid; lia).
assert (Hle : m + 1 <= 2 * m) by lia.
apply Nat.le_trans with (log2 (2 * m)).
- apply log2_monotone; exact Hle.
- rewrite log2_mult_power2; [lia| lia].
}
assert (Hd_le_log2m : d <= log2 m + 1) by lia.
apply Nat.mul_le_mono_pos_l; [lia| exact Hd_le_log2m].
-
set (q := n).
assert (Hq_ge1 : q >= 1) by (subst q; exact Hn).
destruct (build_k_steps_numeric_canonical q Hq_ge1) as
[[d1 [n1 [Hd1 [Hn1 [Hq_entry [Hbuild1 _]]]]]] |
[d1 [n1 [Hd1 [Hn1 [Hodd1 [Hq_entry [Hbuild1 _]]]]]]]].
+
set (K := d + d1).
set (ops := build_k_steps m K).
set (k := d + 2 * d1).
set (m_final := sequence_end q (repeat_R1R0 d1)).
exists K, k, m_final, ops.
split.
*
reflexivity.
* split.
--
subst ops K k.
rewrite build_k_steps_add.
rewrite Hbuild.
assert (Hend0 : sequence_end m (repeat_R0 d) = q).
{ subst q. exact Hseq_end. }
rewrite Hend0.
rewrite Hbuild1.
rewrite app_length.
rewrite repeat_R0_length.
rewrite repeat_R1R0_length.
lia.
-- split.
++
subst ops K.
rewrite build_k_steps_add.
rewrite Hbuild.
assert (Hend0 : sequence_end m (repeat_R0 d) = q).
{ subst q. exact Hseq_end. }
rewrite Hend0.
rewrite Hbuild1.
apply (valid_sequence_app m (repeat_R0 d) (repeat_R1R0 d1)).
** rewrite <- Hbuild. apply build_k_steps_valid; assumption.
** rewrite Hend0.
rewrite <- Hbuild1.
apply build_k_steps_valid.
unfold valid_input in *; lia.
++ split.
**
subst ops K m_final.
rewrite build_k_steps_add.
rewrite Hbuild.
assert (Hend0 : sequence_end m (repeat_R0 d) = q).
{ subst q. exact Hseq_end. }
rewrite Hend0.
rewrite Hbuild1.
rewrite sequence_end_app.
rewrite Hend0.
reflexivity.
** split.
{
subst m_final.
rewrite Hq_entry.
apply R1R0_output_mod6; [exact Hd1 | exact Hn1]. }
{
subst k.
assert (Hd1_le_log2q1 : d1 <= log2 q + 1).
{
assert (Hd1_le_log2qp1 : d1 <= log2 (q + 1)).
{ apply (R1R0_entry_d_log2_bound q d1 n1); try assumption; lia. }
assert (Hlog2q1_le : log2 (q + 1) <= log2 q + 1).
{
assert (Hle : q + 1 <= 2 * q) by lia.
apply Nat.le_trans with (log2 (2 * q)).
- apply log2_monotone. exact Hle.
- rewrite log2_mult_power2; [lia| lia].
}
lia.
}
assert (Hlog2_m : log2 m = log2 q + d).
{
subst q.
assert (Hm_qpow : m = n * 2 ^ d).
{ rewrite Hm_entry. unfold valid_R0R0_entry_number. reflexivity. }
rewrite Hm_qpow.
rewrite log2_mul_pow2; [lia | lia].
}
rewrite Hlog2_m.
apply Nat.le_trans with (d + 2 * (log2 q + 1)).
- apply Nat.add_le_mono_l.
apply Nat.mul_le_mono_pos_l; [lia| exact Hd1_le_log2q1].
- lia. }
+
exfalso.
subst q.
pose proof (valid_R0R0_entry_number_properties d1 n1 Hd1 Hn1) as [_ Heven_q].
unfold is_even in Heven_q.
rewrite <- Hq_entry in Heven_q.
unfold is_odd in Hodd_n.
rewrite Heven_q in Hodd_n.
discriminate.
Qed.

(* Canonical R0 advantage for mod6=2 numbers: two-step chain with positive contribution *)
Theorem mod62_R0advantage_canonical :
  forall m0,
    m0 mod 6 = 2 ->
    exists d0 n0 d1 n1 m1 m2,
      d0 >= 1 /\
      n0 >= 1 /\
      is_odd n0 /\
      m0 = valid_R0R0_entry_number d0 n0 /\
      build_k_steps m0 d0 = repeat_R0 d0 /\
      m1 = sequence_end m0 (repeat_R0 d0) /\
      m1 = n0 /\
      d1 >= 1 /\
      n1 >= 0 /\
      m1 = valid_R1R0_entry_number d1 n1 /\
      build_k_steps m1 d1 = repeat_R1R0 d1 /\
      m2 = sequence_end m1 (repeat_R1R0 d1) /\
      let chains := [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)] in
      valid_chains_condition chains /\
      chains_R0_advantage chains /\
      m2 mod 6 = 2 /\
      sum_contributions (extract_simple_chains chains) = d0 + 1.
Proof.
intros m0 Hm0_mod6.
assert (Hm0_ge1 : m0 >= 1).
{
pose proof (Nat.div_mod m0 6 ltac:(lia)) as Hdiv.
rewrite Hm0_mod6 in Hdiv.
lia.
}
assert (Hm0_even : is_even m0).
{
unfold is_even.
apply Nat.even_spec.
exists (3 * (m0 / 6) + 1).
pose proof (Nat.div_mod m0 6 ltac:(lia)) as Hdiv.
rewrite Hm0_mod6 in Hdiv.
replace (2 * (3 * (m0 / 6) + 1)) with (6 * (m0 / 6) + 2) by ring.
exact Hdiv.
}
destruct (build_k_steps_numeric_canonical m0 Hm0_ge1) as
[[dX [nX [HdX [HnX [Hm0_as_R1R0 [HbuildX _]]]]]] |
[d0 [n0 [Hd0 [Hn0 [Hodd_n0 [Hm0_as_R0R0 [Hbuild0 [Hseq_end0 _]]]]]]]]].
-
exfalso.
pose proof (valid_R1R0_entry_number_is_odd dX nX HdX HnX) as Hodd_m0.
unfold is_odd in Hodd_m0.
unfold is_even in Hm0_even.
rewrite Hm0_as_R1R0 in Hm0_even.
rewrite Hodd_m0 in Hm0_even.
discriminate.
-
set (m1 := sequence_end m0 (repeat_R0 d0)).
assert (Hm1_eq_n0 : m1 = n0).
{ unfold m1. exact Hseq_end0. }
assert (Hm1_ge1 : m1 >= 1).
{ rewrite Hm1_eq_n0. exact Hn0. }
assert (Hodd_m1 : is_odd m1).
{ rewrite Hm1_eq_n0. exact Hodd_n0. }
destruct (build_k_steps_numeric_canonical m1 Hm1_ge1) as
[[d1 [n1 [Hd1 [Hn1 [Hm1_as_R1R0 [Hbuild1 _]]]]]] |
[d1 [n1 [Hd1 [Hn1_ge1 [Hodd_n1 [Hm1_as_R0R0 [Hbuild1 _]]]]]]]].
+
set (m2 := sequence_end m1 (repeat_R1R0 d1)).
assert (Hm2_mod6 : m2 mod 6 = 2).
{
unfold m2.
rewrite Hm1_as_R1R0.
apply R1R0_output_mod6; [exact Hd1 | exact Hn1].
}
assert (Heven_m2 : is_even m2).
{
unfold m2.
destruct (repeat_R1R0_output_even d1 n1 Hd1 Hn1) as [k Hk].
rewrite Hm1_as_R1R0.
rewrite Hk.
apply even_true_implies_even.
apply even_2x.
}
exists d0, n0, d1, n1, m1, m2.
split; [exact Hd0|].
split; [exact Hn0|].
split; [exact Hodd_n0|].
split; [exact Hm0_as_R0R0|].
split; [exact Hbuild0|].
split; [unfold m1; reflexivity|].
split; [exact Hm1_eq_n0|].
split; [exact Hd1|].
split; [exact Hn1|].
split; [exact Hm1_as_R1R0|].
split; [exact Hbuild1|].
split; [unfold m2; reflexivity|].
cbv beta.
set (chains := [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)]).
assert (Hchains_nonempty : chains <> nil).
{ unfold chains; discriminate. }
assert (Hchains_valid : forall bdnds,
In bdnds chains ->
let '(b, dX, nX, mX, SendX) := bdnds in
valid_chain_sequence_condition b dX nX mX SendX).
{
intros bdnds Hin.
unfold chains in Hin.
simpl in Hin.
destruct Hin as [Hin | [Hin | []]]; subst bdnds.
-
unfold valid_chain_sequence_condition.
split; [exact Hd0|].
right.
split; [reflexivity|].
split; [exact Hn0|].
split; [exact Hodd_n0|].
split; [exact Hm0_as_R0R0|].
split; [unfold m1; reflexivity|].
exact Hodd_m1.
-
unfold valid_chain_sequence_condition.
split; [exact Hd1|].
left.
split; [reflexivity|].
split; [exact Hn1|].
split; [exact Hm1_as_R1R0|].
split; [unfold m2; reflexivity|].
exact Heven_m2.
}
assert (Hcond : valid_chains_condition chains).
{
unfold valid_chains_condition.
split; [exact Hchains_nonempty|].
intros bdnds Hin.
exact (Hchains_valid bdnds Hin).
}
assert (Hadv : chains_R0_advantage chains).
{
unfold chains_R0_advantage.
apply (valid_chains_sequence_R0_advantage_corollary chains).
- exact Hchains_nonempty.
- intros bdnds Hin.
exact (Hchains_valid bdnds Hin).
}
split; [exact Hcond|].
split; [exact Hadv|].
split; [exact Hm2_mod6|].
unfold chains; simpl; lia.
+
exfalso.
pose proof (valid_R0R0_entry_number_properties d1 n1 Hd1 Hn1_ge1)
as [_ Heven_m1].
unfold is_even in Heven_m1.
rewrite <- Hm1_as_R0R0 in Heven_m1.
unfold is_odd in Hodd_m1.
rewrite Heven_m1 in Hodd_m1.
discriminate.
Qed.

(* Factor2 decomposition function definitions *)

(* Extract 2-factors from n with bounded iterations *)
Fixpoint factor2_bounded (k n : nat) : nat * nat :=
  match k with
  | 0 => (0, n)
  | S k' =>
      if Nat.even n then
        let '(d, q) := factor2_bounded k' (n / 2) in
        (S d, q)
      else (0, n)
  end.

(* Extract 2-factors from n (full decomposition) *)
Definition factor2 (n : nat) : nat * nat := factor2_bounded n n.
(* Exponent of 2 in n's prime factorization *)
Definition factor2_exp (n : nat) : nat := fst (factor2 n).
(* Odd part of n after removing all factors of 2 *)
Definition factor2_odd (n : nat) : nat := snd (factor2 n).

(* ------------------------------------------------------------------ *)
(* Basic properties of factor2 decomposition functions *)

(* factor2_bounded decomposition: n = q * 2^d *)
Lemma factor2_bounded_decomp : forall k n d q,
  factor2_bounded k n = (d, q) ->
  n = q * 2 ^ d.
Proof.
induction k as [|k IH]; intros n d q H.
-
simpl in H. inversion H; subst.
rewrite Nat.pow_0_r.
rewrite Nat.mul_1_r.
reflexivity.
-
simpl in H.
destruct (Nat.even n) eqn:He.
+
rewrite <- (div2_divmod_eq n) in H.
destruct (factor2_bounded k (n / 2)) as [d0 q0] eqn:Hfb.
simpl in H.
injection H as Hd Hq.
subst d q.
specialize (IH (n / 2) d0 q0 Hfb).
apply Nat.even_spec in He.
destruct He as [t Ht].
assert (Hdiv : n / 2 = t).
{ rewrite Ht. rewrite Nat.mul_comm. apply Nat.div_mul; lia. }
rewrite Hdiv in IH.
rewrite Ht.
rewrite IH.
change (2 ^ (S d0)) with (2 * 2 ^ d0).
ring.
+
inversion H; subst.
rewrite Nat.pow_0_r.
rewrite Nat.mul_1_r.
reflexivity.
Qed.

(* factor2_bounded preserves oddness of the quotient *)
Lemma factor2_bounded_odd : forall k n,
  n >= 1 -> k >= n -> is_odd (snd (factor2_bounded k n)).
Proof.
induction k as [|k IH]; intros n Hn Hkn.
- lia.
- simpl.
destruct (Nat.even n) eqn:He.
+
rewrite <- (div2_divmod_eq n).
apply Nat.even_spec in He.
destruct He as [t Ht].
assert (Ht_ge1 : t >= 1).
{
destruct t as [|t'].
- rewrite Ht in Hn. simpl in Hn. lia.
- lia.
}
assert (Hdiv : n / 2 = t).
{
rewrite Ht.
rewrite Nat.mul_comm.
apply Nat.div_mul.
lia.
}
assert (Hk_ge_t : k >= t).
{
assert (Hk_ge_2t1 : k >= 2 * t - 1) by (rewrite Ht in Hkn; lia).
assert (Ht_le_2t1 : t <= 2 * t - 1) by (destruct t; lia).
lia.
}
assert (Hlet : snd (let '(d, q) := factor2_bounded k (n / 2) in (S d, q)) =
snd (factor2_bounded k (n / 2))).
{ destruct (factor2_bounded k (n / 2)) as [d'' q'']; simpl; reflexivity. }
rewrite Hlet.
apply (IH (n / 2)).
*
rewrite Hdiv.
exact Ht_ge1.
*
rewrite Hdiv.
exact Hk_ge_t.
+
unfold is_odd.
exact He.
Qed.

(* factor2 decomposition: n = odd_part * 2^exponent *)
Lemma factor2_spec_decomp : forall n,
  n = factor2_odd n * 2 ^ (factor2_exp n).
Proof.
intro n.
unfold factor2_odd, factor2_exp, factor2.
remember (factor2_bounded n n) as p eqn:Hp.
destruct p as [d q].
simpl.
symmetry in Hp.
apply (factor2_bounded_decomp n n d q Hp).
Qed.

(* factor2 odd part is always odd for n >= 1 *)
Lemma factor2_spec_odd : forall n,
  n >= 1 -> is_odd (factor2_odd n).
Proof.
intros n Hn.
unfold factor2_odd, factor2.
apply (factor2_bounded_odd n n Hn).
lia.
Qed.

(* Canonical macro-step for mod6=2 *)
Definition canonical_mod62_macrostep_chains (m0 : nat)
  : list (bool * nat * nat * nat * nat) :=
  let '(d0, n0) := factor2 m0 in
  let m1 := n0 in
  let '(d1, q1) := factor2 (m1 + 1) in
  let n1 := q1 / 2 in
  let m2 := sequence_end m1 (repeat_R1R0 d1) in
  [(false, d0, n0, m0, m1); (true, d1, n1, m1, m2)].

(* End state after canonical macro-step for mod6=2 *)
Definition canonical_mod62_macrostep_end (m0 : nat) : nat :=
  let '(d0, n0) := factor2 m0 in
  let m1 := n0 in
  let '(d1, _) := factor2 (m1 + 1) in
  sequence_end m1 (repeat_R1R0 d1).

(* Iterated canonical macro-steps for mod6=2: concatenate chains from t steps *)
Fixpoint canonical_mod62_iterated_chains (t : nat) (m0 : nat)
  : list (bool * nat * nat * nat * nat) :=
  match t with
  | 0 => []
  | S t' =>
      let chains1 := canonical_mod62_macrostep_chains m0 in
      let m2 := canonical_mod62_macrostep_end m0 in
      chains1 ++ canonical_mod62_iterated_chains t' m2
  end.

(* Final state after t iterated canonical macro-steps for mod6=2 *)
Fixpoint canonical_mod62_iterated_end (t : nat) (m0 : nat) : nat :=
  match t with
  | 0 => m0
  | S t' => canonical_mod62_iterated_end t' (canonical_mod62_macrostep_end m0)
  end.

(* Canonical macro-step preserves mod6=2 and has positive contribution *)
Lemma canonical_mod62_macrostep_spec :
  forall m0,
    m0 mod 6 = 2 ->
    let chains := canonical_mod62_macrostep_chains m0 in
    let m2 := canonical_mod62_macrostep_end m0 in
      length chains = 2 /\
      valid_chains_condition chains /\
      m2 mod 6 = 2 /\
      2 <= sum_contributions (extract_simple_chains chains).
Proof.
intros m0 Hm0_mod6.
unfold canonical_mod62_macrostep_chains, canonical_mod62_macrostep_end.
remember (factor2 m0) as p0 eqn:Hp0.
destruct p0 as [d0 n0] eqn:Hp0'.
set (m1 := n0).
assert (Hn0m1 : n0 = m1) by reflexivity.
remember (factor2 (m1 + 1)) as p1 eqn:Hp1.
destruct p1 as [d1 q1] eqn:Hp1'.
set (n1 := q1 / 2).
set (m2 := sequence_end m1 (repeat_R1R0 d1)).
assert (Hm0_ge1 : m0 >= 1).
{
pose proof (Nat.div_mod m0 6 ltac:(lia)) as Hdiv.
rewrite Hm0_mod6 in Hdiv.
lia.
}
assert (Hm0_even : is_even m0).
{
unfold is_even.
apply Nat.even_spec.
exists (3 * (m0 / 6) + 1).
pose proof (Nat.div_mod m0 6 ltac:(lia)) as Hdiv.
rewrite Hm0_mod6 in Hdiv.
replace (2 * (3 * (m0 / 6) + 1)) with (6 * (m0 / 6) + 2) by ring.
exact Hdiv.
}
assert (Hm0_decomp : m0 = n0 * 2 ^ d0).
{
pose proof (factor2_spec_decomp m0) as H.
unfold factor2_odd, factor2_exp in H.
rewrite <- Hp0 in H.
exact H.
}
assert (Hn0_odd : is_odd n0).
{
pose proof (factor2_spec_odd m0 Hm0_ge1) as H.
unfold factor2_odd in H.
rewrite <- Hp0 in H.
exact H.
}
assert (Hn0_ge1 : n0 >= 1).
{
destruct n0 as [|n0'] eqn:Hn0.
- simpl in Hm0_decomp.
lia.
- lia.
}
assert (Hd0_ge1 : d0 >= 1).
{
destruct d0 as [|d0'].
- simpl in Hm0_decomp.
unfold is_even in Hm0_even.
unfold is_odd in Hn0_odd.
rewrite Hm0_decomp in Hm0_even.
rewrite Nat.mul_1_r in Hm0_even.
rewrite Hn0_odd in Hm0_even.
discriminate.
- lia.
}
assert (Hm1_odd : is_odd m1).
{ subst m1. exact Hn0_odd. }
assert (Hm1p1_even : is_even (m1 + 1)).
{
unfold is_even.
replace (m1 + 1) with (S m1) by lia.
rewrite Nat.even_succ.
unfold Nat.odd.
unfold is_odd in Hm1_odd.
rewrite Hm1_odd.
simpl.
reflexivity.
}
assert (Hm1p1_decomp : (m1 + 1) = q1 * 2 ^ d1).
{
pose proof (factor2_spec_decomp (m1 + 1)) as H.
unfold factor2_odd, factor2_exp in H.
rewrite <- Hp1 in H.
exact H.
}
assert (Hq1_odd : is_odd q1).
{
pose proof (factor2_spec_odd (m1 + 1) ltac:(lia)) as H.
unfold factor2_odd in H.
rewrite <- Hp1 in H.
exact H.
}
assert (Hd1_ge1 : d1 >= 1).
{
destruct d1 as [|d1'].
- simpl in Hm1p1_decomp.
unfold is_even in Hm1p1_even.
unfold is_odd in Hq1_odd.
rewrite Hm1p1_decomp in Hm1p1_even.
rewrite Nat.mul_1_r in Hm1p1_even.
rewrite Hq1_odd in Hm1p1_even.
discriminate.
- lia.
}
assert (Hq1_form : q1 = 2 * n1 + 1).
{
subst n1.
assert (Hq1_mod2 : q1 mod 2 = 1).
{
assert (Hodd_bool : Nat.odd q1 = true).
{ unfold Nat.odd. unfold is_odd in Hq1_odd. rewrite Hq1_odd. reflexivity. }
apply Nat.odd_spec in Hodd_bool.
destruct Hodd_bool as [k Hk].
rewrite Hk.
rewrite Nat.mul_comm.
rewrite Nat.add_comm.
rewrite Nat.mod_add by lia.
simpl.
reflexivity.
}
pose proof (Nat.div_mod q1 2 ltac:(lia)) as Hdiv.
rewrite Hq1_mod2 in Hdiv.
exact Hdiv.
}
assert (Hm1_as_R1R0 : m1 = valid_R1R0_entry_number d1 n1).
{
apply (Nat.add_cancel_r _ _ 1).
rewrite valid_R1R0_entry_number_plus1.
rewrite Hm1p1_decomp.
rewrite Hq1_form.
ring.
}
assert (Hm2_mod6 : (sequence_end m1 (repeat_R1R0 d1)) mod 6 = 2).
{
rewrite Hm1_as_R1R0.
apply R1R0_output_mod6; [exact Hd1_ge1 | lia].
}
assert (Hm2_even : is_even (sequence_end m1 (repeat_R1R0 d1))).
{
rewrite Hm1_as_R1R0.
destruct (repeat_R1R0_output_even d1 n1 Hd1_ge1 ltac:(lia)) as [k Hk].
apply even_true_implies_even.
rewrite Hk.
apply even_2x.
}
assert (Hm2_def : m2 = sequence_end m1 (repeat_R1R0 d1)) by reflexivity.
assert (Hm2_even_m2 : is_even m2).
{
rewrite <- Hm2_def in Hm2_even.
exact Hm2_even.
}
cbv beta.
simpl.
split; [reflexivity|].
split.
-
unfold valid_chains_condition.
split.
+ discriminate.
+ intros bdnds Hin.
simpl in Hin.
destruct Hin as [Hin | [Hin | []]]; subst bdnds.
*
unfold valid_chain_sequence_condition.
split; [exact Hd0_ge1|].
right.
repeat split; try reflexivity.
-- exact Hn0_ge1.
-- exact Hn0_odd.
-- unfold valid_R0R0_entry_number.
rewrite Hn0m1 in Hm0_decomp.
exact Hm0_decomp.
--
rewrite Hm0_decomp.
change (n0 * 2 ^ d0) with (valid_R0R0_entry_number d0 n0).
rewrite (repeat_R0_output_reaches_one d0 n0 Hd0_ge1 Hn0_ge1).
rewrite Hn0m1.
reflexivity.
-- exact Hn0_odd.
*
unfold valid_chain_sequence_condition.
split; [exact Hd1_ge1|].
left.
split; [reflexivity|].
split; [lia|].
split; [exact Hm1_as_R1R0|].
split.
-- symmetry. exact Hm2_def.
-- exact Hm2_even_m2.
- split.
+
exact Hm2_mod6.
+
simpl.
lia.
Qed.

(* Iterated canonical macro-steps for mod6=2: lower bound on total contributions *)
Theorem mod62_macrostep_iterated_lower_bound_canonical :
  forall t m0,
    t >= 1 ->
    m0 mod 6 = 2 ->
    let chains := canonical_mod62_iterated_chains t m0 in
    let mt := canonical_mod62_iterated_end t m0 in
      length chains = 2 * t /\
      valid_chains_condition chains /\
      mt mod 6 = 2 /\
      2 * t <= sum_contributions (extract_simple_chains chains) /\
      chains_R0_advantage chains.
Proof.
intros t m0 Ht Hm0.
cbv beta.
revert m0 Ht Hm0.
induction t as [|t IH]; intros m0 Ht Hm0.
- lia.
-
set (chains1 := canonical_mod62_macrostep_chains m0).
set (m2 := canonical_mod62_macrostep_end m0).
pose proof (canonical_mod62_macrostep_spec m0 Hm0) as Hstep.
cbv beta in Hstep.
destruct Hstep as [Hlen1 [Hvalid1 [Hm2_mod6 Hsum1]]].
destruct t as [|t'].
+
subst chains1 m2.
simpl.
rewrite app_nil_r.
rewrite Hlen1.
split; [lia|].
split; [exact Hvalid1|].
split; [exact Hm2_mod6|].
split.
*
replace (2 * 1) with 2 by lia.
exact Hsum1.
*
destruct Hvalid1 as [Hne Hall].
unfold chains_R0_advantage.
apply (valid_chains_sequence_R0_advantage_corollary (canonical_mod62_macrostep_chains m0)).
-- exact Hne.
-- intros bdnds Hin.
exact (Hall bdnds Hin).
+
assert (Ht_ge1 : S t' >= 1) by lia.
specialize (IH m2 Ht_ge1 Hm2_mod6).
remember (canonical_mod62_iterated_chains (S t') m2) as chains_rest eqn:Hrest.
destruct IH as [Hlen_rest [Hvalid_rest [Hmt_mod6 [Hsum_rest _]]]].
set (chains := chains1 ++ chains_rest).
assert (Hlen : length chains = 2 * S (S t')).
{
subst chains.
subst chains1.
rewrite app_length.
rewrite Hlen1.
rewrite Hlen_rest.
lia.
}
assert (Hvalid : valid_chains_condition chains).
{
subst chains.
unfold valid_chains_condition in *.
destruct Hvalid1 as [Hne1 Hall1].
destruct Hvalid_rest as [Hne2 Hall2].
split.
- intro Hcontra.
apply app_eq_nil in Hcontra.
destruct Hcontra as [Hc1 _].
destruct (canonical_mod62_macrostep_chains m0); simpl in Hc1; discriminate.
- intros bdnds Hin.
apply in_app_or in Hin.
destruct Hin as [Hin | Hin].
+ exact (Hall1 bdnds Hin).
+ exact (Hall2 bdnds Hin).
}
assert (Hsum : 2 * S (S t') <= sum_contributions (extract_simple_chains chains)).
{
subst chains.
subst chains1.
rewrite extract_simple_chains_app.
rewrite sum_contributions_app.
rewrite Nat.mul_succ_r.
rewrite Nat.add_comm.
apply (Nat.add_le_mono _ _ _ _ Hsum1 Hsum_rest).
}
assert (Hadv : chains_R0_advantage chains).
{
destruct Hvalid as [Hne Hall].
unfold chains_R0_advantage.
apply (valid_chains_sequence_R0_advantage_corollary chains).
- exact Hne.
- intros bdnds Hin.
exact (Hall bdnds Hin).
}
assert (Hchains_eq : canonical_mod62_iterated_chains (S (S t')) m0 = chains).
{
subst chains.
cbn [canonical_mod62_iterated_chains].
cbv beta.
fold (canonical_mod62_iterated_chains (S t') (canonical_mod62_macrostep_end m0)).
subst chains1 m2.
rewrite Hrest.
reflexivity.
}
split; [rewrite Hchains_eq; exact Hlen|].
split; [rewrite Hchains_eq; exact Hvalid|].
split; [exact Hmt_mod6|].
split; [rewrite Hchains_eq; exact Hsum|].
rewrite Hchains_eq; exact Hadv.
Qed.

(* Global advantage growth for mod6=2: linear growth of contributions *)
Theorem global_mod62_advantage_growth_canonical :
  forall m t,
    valid_input m ->
    t >= 1 ->
    exists (K k : nat) (m2 mt : nat)
           (ops : list CollatzOp)
           (chains : list (bool * nat * nat * nat * nat)),
      ops = build_k_steps m K /\
      length ops = k /\
      valid_sequence ops m /\
      sequence_end m ops = m2 /\
      k <= 2 * (log2 m + 1) /\
      m2 mod 6 = 2 /\
      chains = canonical_mod62_iterated_chains t m2 /\
      mt = canonical_mod62_iterated_end t m2 /\
      length chains = 2 * t /\
      valid_chains_condition chains /\
      mt mod 6 = 2 /\
      2 * t <= sum_contributions (extract_simple_chains chains) /\
      chains_R0_advantage chains.
Proof.
intros m t Hm_valid Ht.
destruct (direct_conversion_to_mod6_2_orbit_canonical m Hm_valid)
as [K [k [m2 [ops
[Hops_eq [Hops_len [Hops_valid [Hops_end [Hm2_mod6 Hk_bound]]]]]]]]].
pose proof (mod62_macrostep_iterated_lower_bound_canonical t m2 Ht Hm2_mod6) as Hiter.
cbv beta in Hiter.
destruct Hiter as [Hchains_len [Hchains_valid [Hmt_mod6 [Hsum_lower Hadv]]]].
exists K, k, m2, (canonical_mod62_iterated_end t m2),
ops, (canonical_mod62_iterated_chains t m2).
split; [exact Hops_eq|].
split; [exact Hops_len|].
split; [exact Hops_valid|].
split; [exact Hops_end|].
split; [exact Hk_bound|].
split; [exact Hm2_mod6|].
split; [reflexivity|].
split; [reflexivity|].
split; [exact Hchains_len|].
split; [exact Hchains_valid|].
split; [exact Hmt_mod6|].
split; [exact Hsum_lower|].
exact Hadv.
Qed.
