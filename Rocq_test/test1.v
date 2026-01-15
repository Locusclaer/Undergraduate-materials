(* 定义全局变量 f1 为函数 f(a,b,c) = b*b - 4*a*c，参数和返回值类型为整数 *)
Require Import ZArith. (* Rocq标准库，用于基本整数 *)
Open Scope Z_scope. (* 打开整数辖域 *)

(* test1 *)
Definition f1 (a b c : Z) : Z := b * b - 4 * a * c. (* 定义全局变量 f1 为函数*)

(* 检查 f1 的类型 *)
Check f1.  (* 输出: f1 : Z -> Z -> Z -> Z *)

(* 当 a=4, b=5, c=1 时计算函数值 *)
Compute f1 4 5 1.  (* 输出: 9 : Z *)



(* test2 *)
Section SumFour.
  Variable a b c d : Z.  (* 局部变量，会在Section外自动抽象为参数 *)

  (* 定义f2为四个整数的和，这里不写任何函数参数 *)
  Definition f2 : Z := a + b + c + d.
End SumFour.



(* 打印f2函数，观察自动生成的参数抽象 *)
Print f2.  (* 输出: f2 = fun a b c d : Z => a + b + c + d : Z -> Z -> Z -> Z -> Z *)


(* 调用函数，参数为1,2,3,4 *)
Compute f2 1 2 3 4.  (* 输出: 10 *)

(* test3 *)
(* 定义函数f3，使用fun =>形式，只能使用Zplus和Zmult *)
Definition f3 : Z -> Z := fun x : Z => 
    Zplus (Zmult 2 (Zmult x x)) (Zplus (Zmult 3 x) 3).


(* 计算f3在x=2时的值 *)
Compute f3 2.  (* 预期结果: 17 *)


(* 计算f3在x=3时的值 *)
Compute f3 3.  (* 预期结果: 30 *)


(* 计算f3在x=4时的值 *)
Compute f3 4.  (* 预期结果: 47 *)