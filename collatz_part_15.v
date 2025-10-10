Load "collatz_part_14.v".



Require Import Lia.

(* 利用规范分解分别推出 d 的对数上界（R1R0 分支） *)
Lemma canonical_R1R0_d_log2_bound :
  forall m d n,
    m >= 1 ->
    m = valid_R1R0_entry_number d n ->
    d >= 1 -> n >= 0 ->
    2 ^ d <= m + 1 /\ d <= log2 (m + 1).
Proof.
intros m d n Hm Hrepr Hd Hn.
(* 展开并化简：m+1 = 2^d * (2n+1) *)
unfold valid_R1R0_entry_number in Hrepr.
assert (Hpow: 2 ^ d <= m + 1).
{ rewrite Hrepr. lia. }
split.
- exact Hpow.
- (* 从 2^d <= m+1 推出 d <= log2(m+1) *)
  assert (Hpos: m + 1 >= 1) by lia.
  pose proof (Nat.log2_spec (m + 1) Hpos) as [_ Hhigh].
  destruct (Nat.le_gt_cases d (log2 (m + 1))) as [Hle | Hgt].
  + exact Hle.
  + (* d > log2(m+1) 则 S (log2 ...) <= d，从而 2^(S log2) <= 2^d 且 m+1 < 2^(S log2)，矛盾 *)
    assert (Hge: S (log2 (m + 1)) <= d) by lia.
    assert (Hpow2: 2 ^ (S (log2 (m + 1))) <= 2 ^ d) by (apply Nat.pow_le_mono_r; lia).
    lia.
Qed.

(* R0R0 分支 *)
Lemma canonical_R0R0_d_log2_bound :
  forall m d n,
    m >= 1 ->
    m = valid_R0R0_entry_number d n ->
    d >= 1 -> n >= 1 ->
    2 ^ d <= m /\ d <= log2 m.
Proof.
intros m d n Hm Hrepr Hd Hn.
unfold valid_R0R0_entry_number in Hrepr.
(* m = n * 2^d, with n >= 1, so 2^d <= m *)
assert (Hpow: 2 ^ d <= m).
{ rewrite Hrepr. 
  assert (Hpow_pos: 2^d > 0) by (apply gt_0_2_pow; exact Hd).
  rewrite <- Nat.mul_1_l at 1.
  apply Nat.mul_le_mono_r; lia. }
split.
- exact Hpow.
- (* 从 2^d <= m 推出 d <= log2 m *)
  assert (Hpos: m >= 1) by lia.
  pose proof (Nat.log2_spec m Hpos) as [_ Hhigh].
  destruct (Nat.le_gt_cases d (log2 m)) as [Hle | Hgt].
  + exact Hle.
  + assert (Hge: S (log2 m) <= d) by lia.
    assert (Hpow2: 2 ^ (S (log2 m)) <= 2 ^ d) by (apply Nat.pow_le_mono_r; lia).
    lia.
Qed.

(* 统一包装：对任意规范分支都有 d <= log2 (m+2) *)
Lemma canonical_d_log2_global :
  forall m d n,
    m >= 1 ->
    ( (m = valid_R1R0_entry_number d n /\ d >= 1 /\ n >= 0)
    \/ (m = valid_R0R0_entry_number d n /\ d >= 1 /\ n >= 1) ) ->
    d <= log2 (m + 2).
Proof.
intros m d n Hm [Hcase | Hcase].
- destruct Hcase as [Hrepr [Hd Hn]].
  pose proof (canonical_R1R0_d_log2_bound m d n Hm Hrepr Hd Hn) as [Hpow Hlog].
  (* Hlog: d <= log2 (m+1); 且 m+1 <= m+2 *)
  apply Nat.le_trans with (log2 (m+1)); [exact Hlog|].
  apply log2_monotone. lia.
- destruct Hcase as [Hrepr [Hd Hn]].
  pose proof (canonical_R0R0_d_log2_bound m d n Hm Hrepr Hd Hn) as [Hpow Hlog].
  (* d <= log2 m <= log2 (m+2) *)
  apply Nat.le_trans with (log2 m); [exact Hlog|].
  apply log2_monotone. lia.
Qed.

(* 直接从 build_k_steps_numeric_canonical 得到全局上界 *)
Corollary build_k_steps_numeric_canonical_d_log2_global :
  forall m d,
    m >= 1 ->
    (exists n0, m = valid_R1R0_entry_number d n0 /\ d >= 1 /\ n0 >= 0
         \/ m = valid_R0R0_entry_number d n0 /\ d >= 1 /\ n0 >= 1) ->
    d <= log2 (m + 2).
Proof.
intros m d Hm Hexists.
destruct Hexists as [n0 Hor].
destruct Hor as [Hcase | Hcase].
- destruct Hcase as [Hrepr [Hd Hn]].
  apply (canonical_d_log2_global m d n0 Hm). left; repeat split; assumption.
- destruct Hcase as [Hrepr [Hd Hn]].
  apply (canonical_d_log2_global m d n0 Hm). right; repeat split; assumption.
Qed.

(* 将对数上界与构造序列本身的模式长度联系起来 *)
Lemma build_k_steps_prefix_length_log2 :
  forall m d n,
    m >= 1 ->
    ( (m = valid_R1R0_entry_number d n /\ d >= 1 /\ n >= 0 /\ build_k_steps m d = repeat_R1R0 d)
    \/ (m = valid_R0R0_entry_number d n /\ d >= 1 /\ n >= 1 /\ build_k_steps m d = repeat_R0 d)) ->
    (length (build_k_steps m d) = 2 * d \/ length (build_k_steps m d) = d) /\ d <= log2 (m + 2).
Proof.
  intros m d n Hm [Hr1 | Hr0].
  - destruct Hr1 as [Hrepr [Hd [Hn Hseq]]].
    split.
    + left. rewrite Hseq. apply repeat_R1R0_length.
    + apply (canonical_d_log2_global m d n Hm). left; repeat split; assumption.
  - destruct Hr0 as [Hrepr [Hd [Hn Hseq]]].
    split.
    + right. rewrite Hseq. apply repeat_R0_length.
    + apply (canonical_d_log2_global m d n Hm). right; repeat split; assumption.
Qed.

(* 序列前 d 步对应规范分支 ⇒ 直接得到长度 ≤ 2*log2(m+2) *)
Lemma build_k_steps_prefix_log2_bound : forall m d n,
  m >= 1 ->
  ( (m = valid_R1R0_entry_number d n /\ d >= 1 /\ n >= 0 /\ build_k_steps m d = repeat_R1R0 d)
  \/ (m = valid_R0R0_entry_number d n /\ d >= 1 /\ n >= 1 /\ build_k_steps m d = repeat_R0 d)) ->
  length (build_k_steps m d) <= 2 * log2 (m + 2).
Proof.
  intros m d n Hm Hcases.
  destruct (build_k_steps_prefix_length_log2 m d n Hm Hcases) as [Hlen_or Hdb].
  destruct Hlen_or as [Hr1len | Hr0len].
  - rewrite Hr1len. apply Nat.mul_le_mono_pos_l; [lia|exact Hdb].
  - rewrite Hr0len. (* d <= log2(m+2) <= 2*log2(m+2) *)
    apply Nat.le_trans with (2 * d).
    + replace (2 * d) with (d + d) by lia.
      apply Nat.le_add_r.
    + apply Nat.mul_le_mono_pos_l; [lia|exact Hdb].
Qed.

(* 从主规范定理直接派生：存在分支使前 d 步长度 ≤ 2*log2(m+2) *)
Corollary build_k_steps_numeric_canonical_length_log2 : forall m,
  m >= 1 ->
  exists d,
    d >= 1 /\ d <= log2 (m + 2) /\
    (exists ops, build_k_steps m d = ops /\ length ops <= 2 * log2 (m + 2)).
Proof.
  intros m Hm.
  destruct (build_k_steps_numeric_canonical m Hm) as
  [ [d [n [Hd [Hn [Hmrepr [Hseq Hbounds] ]]]]] | [d [n [Hd [Hn [Hodd [Hmrepr [Hseq [Hend Huniq]]]]]]]] ].
  - exists d; repeat split; try assumption.
    + apply (canonical_d_log2_global m d n Hm). left; repeat split; assumption.
    + exists (repeat_R1R0 d). split.
      * rewrite <- Hseq. reflexivity.
      * rewrite repeat_R1R0_length.
        apply Nat.mul_le_mono_pos_l; [lia|].
        apply (canonical_d_log2_global m d n Hm). left; repeat split; assumption.
  - exists d; repeat split; try assumption.
    + apply (canonical_d_log2_global m d n Hm). right; repeat split; assumption.
    + exists (repeat_R0 d). split.
      * rewrite <- Hseq. reflexivity.
      * rewrite repeat_R0_length.
        eapply Nat.le_trans.
        { apply (canonical_d_log2_global m d n Hm). right; repeat split; assumption. }
        { apply Nat.le_add_r. }
Qed.

