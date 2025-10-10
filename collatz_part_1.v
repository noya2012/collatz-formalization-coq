Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Lia.     (* 引入lia策略，这是更新的线性整数算术求解器 *)
Require Import PeanoNat.
Require Import Ring.
Require Import Arith.   (* 引入算术运算 *)
Require Import ArithRing.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Div2.
Load "log2_p.v".

(* noya2012@126.com 306000250@qq.com  zeng  *)
(* 定义考拉兹操作   文档使用coq ide8.9 版本*)
Inductive CollatzOp : Type :=
  | R0 : CollatzOp
  | R1 : CollatzOp.

(* 定义合法输入的性质 *)
Definition valid_input (n: nat) := n >= 1.

(* 辅助定义：将bool转换为Prop *)
Definition is_even (n: nat) := Nat.even n = true.
Definition is_odd (n: nat) := Nat.even n = false.

(* 定义单步考拉兹操作 *)
Definition collatz_step (n : nat) : nat :=
  if Nat.even n then n / 2
  else 3 * n + 1.

(* 入口函数定义 *)
Definition valid_R0R1_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 2).

(* 定义入口函数 *)
Definition valid_R0R0_entry_number (d n: nat) : nat :=
  n * (2^d).

(* R1R0 入口函数定义 *)
Definition valid_R1R0_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 1).





(* 定义计数函数 *)
Fixpoint count_R0 (ops: list CollatzOp) : nat :=
match ops with
| [] => 0
| R0 :: rest => S (count_R0 rest)
| R1 :: rest => count_R0 rest
end.

(* r1计数函数 *)
Fixpoint count_R1 (ops: list CollatzOp) : nat :=
match ops with
| [] => 0
| R0 :: rest => count_R1 rest
| R1 :: rest => S (count_R1 rest)
end.



(* 定义序列中R0和R1的计数函数 *)
Fixpoint count_operations (ops: list CollatzOp) : (nat * nat) :=
  match ops with
  | nil => (0, 0)
  | op :: rest =>
    let (r0s, r1s) := count_operations rest in
    match op with
    | R0 => (S r0s, r1s)
    | R1 => (r0s, S r1s)
    end
  end.




(* 定义有效操作 *)
Definition valid_operation (n: nat) (op: CollatzOp) : Prop :=
  match op with
  | R0 => is_even n
  | R1 => is_odd n
  end.

(* 定义序列中第k个值 *)
Fixpoint nth_sequence_value (n: nat) (k: nat) : nat :=
  match k with
  | 0 => n
  | S k' => collatz_step (nth_sequence_value n k')
  end.

(* 定义序列的最终值 *)
Definition sequence_end (n: nat) (ops: list CollatzOp) : nat :=
  nth_sequence_value n (length ops).
  
(* 定义序列的有效性：序列中的每个操作都是合法的 *)
Definition valid_sequence (ops: list CollatzOp) (n: nat) : Prop :=
  forall i, i < length ops ->
    valid_operation (nth_sequence_value n i) (nth i ops R0).


(* R0模式的重复构造函数 - 可以处理单个R0和连续R0 *)
Fixpoint repeat_R0 (d: nat) : list CollatzOp :=
  match d with
  | 0 => []
  | S d' => R0 :: repeat_R0 d'
  end.
(*    该函数构造一个操作列表，包含D个连续的R1R0操作对 *)
Fixpoint repeat_R1R0 (d: nat) : list CollatzOp :=
  match d with
  | 0 => []
  | S d' => R1 :: R0 :: repeat_R1R0 d'
  end.
  
(* 连续R0模式计数函数 *)
Fixpoint count_consecutive_R0 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | R0 :: rest => 1 + count_consecutive_R0 rest
  | _ => 0
  end.

(* 连续R1R0模式的计数 *)
Fixpoint count_consecutive_R1R0 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | [_] => 0
  | R1 :: R0 :: rest => S (count_consecutive_R1R0 rest)
  | _ :: rest => count_consecutive_R1R0 rest
  end.
  
(* 主定理结构*)
Fixpoint build_k_steps (n: nat) (k: nat) : list CollatzOp :=
  match k with
  | 0 => []
  | S k' =>
    let prev_ops := build_k_steps n k' in
    let curr_n := sequence_end n prev_ops in
    if Nat.even curr_n
    then prev_ops ++ [R0]          (* 偶数：添加R0 *)
    else prev_ops ++ [R1; R0]      (* 奇数：添加R1R0 *)
  end.
  
