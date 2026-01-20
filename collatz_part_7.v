Load "collatz_part_6.v".


(* When the sequence starts with R0, consecutive R1R0 count and R1 count remain unchanged *)
Lemma congruent_R0_prefix: forall t2,
  count_consecutive_R1R0 (R0 :: t2) = count_consecutive_R1R0 t2 /\
  count_R1 (R0 :: t2) = count_R1 t2.
Proof.
intros t2.
destruct t2 as [| h t2'].
-
simpl. split; reflexivity.
- destruct t2' as [| h2 t2''].
+
simpl. split; reflexivity.
+
simpl. split; reflexivity.
Qed.




(* Connection property of nth_sequence_value *)
Lemma nth_sequence_value_app : forall n k1 k2,
  nth_sequence_value n (k1 + k2) = nth_sequence_value (nth_sequence_value n k1) k2.
Proof.
intros n k1 k2.
induction k2 as [|k2' IH].
-
simpl. rewrite Nat.add_0_r. reflexivity.
-
rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

(* Connection property of sequence end value *)
Lemma sequence_end_app : forall n ops1 ops2,
  sequence_end n (ops1 ++ ops2) = sequence_end (sequence_end n ops1) ops2.
Proof.
intros n ops1 ops2.
unfold sequence_end.
rewrite app_length.
rewrite nth_sequence_value_app.
reflexivity.
Qed.

