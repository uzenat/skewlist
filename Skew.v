Require Import Arith List Omega.

(** * Skew Binary Numbers, and application to Fast-Access Lists *)

(** Pierre Letouzey, (c) 2016. Version 1.0 9/2/2015 *)

(** This file is compatible with Coq 8.4 or 8.5. *)

(** Source: Okasaki's book "Purely Functional Data Structures". *)

(* Nota: all comments except this one are in CoqDoc syntax,
   hence the leading **, and the first [  ] around all Coq elements. *)


(** ** Misc Coq setup *)

(** Notations [[]] for [nil] and [[a;b;c]] for [a::b::nil] : *)
Import ListNotations.

(** Some compatibility between Coq 8.4 and Coq 8.5 : *)
Require Import NPeano.
Infix "=?" := Nat.eqb.
Set Asymmetric Patterns.

(** Some customizations of the [auto] tactic : *)
Hint Extern 10 (@eq nat _ _) => omega.
Hint Extern 10 (_ <= _) => omega.
Hint Extern 10 (_ < _) => omega.

(** A short alias for the [inversion] tactic : *)
Ltac inv := inversion 1; subst; simpl; auto.
Ltac ind n := induction n;subst;simpl in *;auto.


(** ** PART I : Skew Binary Numbers *)

(** *** Definition of decompositions *)

(** [ones n] is the natural number with [n] times the digit 1,
    that is [2^n - 1]. Using a direct recursive definition helps
    in some proofs below. *)
Fixpoint ones n :=
 match n with
 | 0 => 0
 | S n => 2 * ones n + 1
 end.

(** Some properties of [ones] *)


Lemma pow_minus_1 n:
  2^n - 1 + 1 = 2^n.
Proof.
  ind n.
Qed.
  
Lemma ones_pow n : ones n = 2^n-1.
Proof.
  ind n.
  rewrite <- !plus_n_O.
  rewrite IHn.
  rewrite <- plus_assoc.
  rewrite pow_minus_1.
  omega.
Qed.

Lemma ones_pos n : 0 < n -> 0 < ones n.
Proof.
  inv.
Qed.
  

Lemma ones_le_mono :forall n m,  n <= m -> ones n <= ones m.
Proof.
  intros.
  induction H.
  auto.
  simpl. auto.
Qed.  
  
  
Lemma ones_lt_mono n m : n < m -> ones n < ones m.
Proof.
  intros.
  induction H;simpl;rewrite <- plus_n_O;omega.
Qed.
  
(** [sum_ones [a;b;...]] is the sum [(2^a-1)+(2^b-1)+...].
    If [n] is the obtained numbers, we say that the list
    [[a;b;...]] is a skew binary decomposition of [n]. *)
Fixpoint sum_ones l :=
  match l with
  | nil => 0
  | n :: l' => ones n + sum_ones l'
  end.

(** Some properties of [sum_ones] *)

Lemma sum_ones_app l l' :
 sum_ones (l++l') = sum_ones l + sum_ones l'.
Proof.
  ind l.
Qed.

Lemma sum_ones_rev l :
  sum_ones (rev l) = sum_ones l.
Proof.
  ind l.
  rewrite sum_ones_app.
  simpl.
  auto.
Qed.

(** *** Canonical decompositons *)

(** Not all decompositions of [n] are interesting. For instance,
    the decomposition [1;1;...;1] always exists, but is quite
    boring. And a [0] in arev l ++ [a] decomposition doesn't add anything.
    We'll now consider the canonical decompositions of the form
    [[a;b;c;d;...]] with [0<a<=b<c<d<...] :
    all factors in these decompositions are strictly positive, and
    only the smallest factor may be repeated (at most twice),
    all the other factors appear only once.
    This is expressed by the [Skew] predicate below. It uses
    the [Incr] predicate that expresses that a list is strictly
    increasing. *)

Inductive Incr : list nat -> Prop :=
 | IncrNil : Incr []
 | IncrOne n : Incr [n]
 | IncrCons n m l : n < m -> Incr (m::l) -> Incr (n :: m :: l).

Check Incr.

Inductive Skew : list nat -> Prop :=
 | SkewNil : Skew []
 | SkewOne n : 0 < n -> Skew [n]
 | SkewCons n m l : 0 < n <= m -> Incr (m :: l) -> Skew (n::m::l).

Hint Constructors Skew Incr.

Lemma skew_examples : Skew [2;2;5;7] /\ Skew [1;2;3].
Proof.
 auto.
Qed.
  
(** Some properties of the [Skew] and [Incr] predicates *)


Lemma Incr_Skew m l : Incr (m::l) -> 0 < m -> Skew (m::l).
Proof.
  inv.
Qed.

Lemma Skew_inv n l : Skew (n::l) -> Skew l.
Proof.
  inv.
  apply Incr_Skew;auto.
Qed.


(** The main result is now that any natural number admits one
    and only one canonical skew binary decomposition. *)


(** *** Existence *)

(** For the "exist" part of the statement, we can even build
    the decomposition of [n+1] explicitely out of the
    decomposition of [n]. *)

(** Nota: the syntax [n =? m] is a boolean equality test [Nat.eqb].
    For reasoning about it, you can do a [case Nat.eqb_spec] when
    your goal contains a [=?]. *)

Definition next l :=
  match l with
  | n::m::l' => if n =? m then (S n) :: l' else 1::l
  | _ => 1::l
  end.

Lemma next_sum l : sum_ones (next l) = S (sum_ones l).
Proof.
  ind l.
  destruct l;simpl;auto.
  case Nat.eqb_spec.
  intros;simpl;rewrite <- !plus_n_O;rewrite e;auto.
  intros;simpl;auto.
Qed.  


Lemma gg m n :m < n -> S m <= n.
Proof.
  omega.
Qed.

Lemma gz m n l0:  Incr (m :: n :: l0) -> m < n.
Proof.
  inv.
Qed.

Lemma next_skew l : Skew l -> Skew (next l).
Proof.
  inv.
  case Nat.eqb_spec;auto.
  intros;subst.
  destruct l0;simpl;auto.
  apply SkewCons.
  split;simpl;auto.
  apply gz in H1;auto.
  inversion H1;auto.
Qed.


 (** analyse de l0 et regarder ce qui en sort pour en déduir la fin*)

 (** So the decomposition of [n] is obtained by repeating
    [n] times the [next] function. *)

Fixpoint iter_next n :=
 match n with
 | 0 => nil
 | S n => next (iter_next n)
 end.

Lemma iter_next_sum n : sum_ones (iter_next n) = n.
Proof.
  induction n;simpl;auto.
  rewrite next_sum.
  auto.
Qed.  
  

Lemma iter_next_skew n : Skew (iter_next n).
Proof.
  induction n;simpl;auto.
  apply next_skew;auto.
Qed.


(** Hence the existence statement: *)

Lemma decomp_exists : forall n, exists l, sum_ones l = n /\ Skew l.
Proof.
  intros.
  exists (iter_next n).
  split.
  rewrite iter_next_sum.
  auto.
  apply iter_next_skew.
Qed.

Lemma decomp_exists' : forall n, exists l, Skew l -> sum_ones l = n.
Proof.
  intros.
  exists (iter_next n).
  intros.
  rewrite iter_next_sum.
  auto.
Qed.



(** *** Reversed canonical decomposition *)

(** For the unicity of the decomposition, we have to study the
    largest factor. For that, it is quite easier to consider
    a decomposition sorted in decreasing order : the largest
    factor will come first in the list.
    The [Weks] predicate is equivalent to [Skew] on the mirror
    list. Its definition is standalone, but we'll also need
    later a [Decr] predicate stating that a list is strictly
    decreasing. *)

Inductive Weks : list nat -> Prop :=
 | WeksNil : Weks []
 | WeksOne n : 0 < n -> Weks [n]
 | WeksTwo n : 0 < n -> Weks [n;n]
 | WeksCons n m l : m < n -> Weks (m::l) -> Weks (n::m::l).

Inductive Decr : list nat -> Prop :=
 | DecrNil : Decr []
 | DecrOne n : Decr [n]
 | DecrCons n m l : m < n -> Decr (m :: l) -> Decr (n :: m :: l).

Hint Constructors Weks Decr.

(** Let's now prove equivalences between [Skew] and [Weks]. *)

Lemma Incr_last l n m :
  Incr (l++[n]) -> n < m -> Incr (l++[n;m]).
Proof.
  ind l.
  intros.
  destruct l;simpl in *;auto;inversion H;auto.
Qed.


Lemma Decr_last l n m :
  Decr (l++[n]) -> m < n -> Decr (l++[n;m]).
Proof.
  ind l.
  intros.
  destruct l;simpl;auto;inversion H;auto.
Qed.


Lemma Incr_Decr l : Incr l -> Decr (rev l).
Proof.
  ind l;intros.
  destruct l;simpl;auto.
  rewrite <- app_assoc;simpl.
  inversion H;apply IHl in H4.
  apply Decr_last;auto.
Qed.


(** Un lemme pas si facile *)
Lemma Skew_last l n m :
  Skew (l++[n]) -> n < m -> Skew (l++[n;m]).
Proof.
  ind l;intros.
  apply SkewCons;auto.
  split;inversion H;auto.
  destruct l;simpl in *;auto.
  inversion H;auto.
  inversion H;apply SkewCons;auto.
  apply (Incr_last (n0 :: l) n m) in H5;simpl in *;auto.
Qed.


Lemma tt a l : Decr (a :: l) ->  Decr (l).
Proof.
  inv.
Qed.


Lemma Weks_last l n m :
 Decr (l++[n]) -> 0 < m <= n -> Weks (l++[n;m]).
Proof.
  ind l.
  intros.
  case H0.
  intros;case H2;auto.
  intros;simpl;auto.
  destruct l;simpl in *;auto;inversion H;auto.
Qed.


Lemma Incr_inf_last  n0 n a:  Incr ([n0; n; a])  -> n < a.
Proof.
  inv;inversion H4;auto.
Qed.


Lemma Incr_App_inf_last l n0 n a:  Incr (l ++ [n0; n; a])  -> n < a.
Proof.
  induction l;simpl.
  intros;inversion H;inversion H4;auto.
  intros;simpl in *;auto.
  apply IHl.
  inversion H;auto.
Qed.


Lemma Incr_inv a l : Incr (a :: l) ->  Incr l.
Proof.
  inv.
Qed.

Lemma  Incr_inv_app l n0 n a : Incr (l ++ [n0; n; a]) ->  Incr (l ++ [n0; n]).
Proof.  
  induction l;simpl;auto.
  intros.
  apply IncrCons;auto.
  inversion H;auto.
  destruct l;simpl in *;auto.
  intros;inversion H.
  apply IncrCons;auto.

  intros.
  apply IncrCons.
  inversion H;auto.
  apply Incr_inv in H.
  apply IHl.
  auto.
Qed.
  
Lemma Skew_app_inf_last l n0 n a:  Skew (l ++ [n0; n; a])  -> n < a.
Proof.
  induction l.
  inv.
  inversion H4;auto.
  intros.
  apply IHl.
  inversion H.
  auto.
  apply Incr_Skew in H3.
  auto.
  omega.
Qed.


Lemma Weks_Skew1 l : Weks l -> Skew (rev l).
Proof.
  induction l;simpl in *;auto.
  inv.
  rewrite <- app_assoc;simpl in *.
  apply Skew_last;auto.
Qed.  


Lemma  Skew_inv_last l n0 n a : Skew (l ++ [n0;n;a]) -> Skew (l++[n0;n]).
Proof.
  induction l;simpl;auto.
  intros;inversion H;auto.
  intros.
  destruct l;simpl in *;auto.
  apply SkewCons;inversion H;auto.
  apply IncrCons;inversion H4;auto.
  constructor;inversion H;auto.
  inversion H.
  apply Incr_inv in H9.
  apply Incr_inv_app in H9.
  destruct l;simpl in *;auto.
  apply IncrCons.
  inversion H9;auto.
  inversion H4;auto.
  apply IncrCons;auto.
  inversion H9;auto.
  apply IncrCons.
  inversion H4;auto.
  auto.
Qed.  

Lemma list_empty_no l (a : nat) :
  [] <> l ++ [a].
Proof.
  induction l;simpl;auto.
  discriminate.
  intros.
  discriminate.
Qed.  

Lemma list_empty_no2 l (a0 a1 : nat) :
  [] = l ++ [a0 ; a1] -> False.
Proof.
  induction l;simpl;auto.
  discriminate.
  intros.
  discriminate.
Qed.  

Lemma list_empty_no3 l (n0 a0 a1 : nat) :
  [n0] = l ++ [a0 ; a1] -> False.
Proof.
  induction l;simpl;auto.
  discriminate.
  intros.
  destruct l;simpl in *;auto.
  discriminate.
  discriminate.
Qed. 

Lemma Weks_Skew2 l : Skew (rev l) -> Weks l.
Proof.
  ind l.
  intros.
  destruct l;simpl in *;auto.
  inversion H;auto.
  destruct l;simpl in *;auto.
  inversion H;auto.
  case H2.
  intros.
  case H6;auto.
  rewrite <- !app_assoc in *;simpl in *.
  apply WeksCons.
  apply Skew_app_inf_last in H;auto.
  apply Skew_inv_last in H;auto.
Qed.
 

Lemma Weks_Skew l : Skew (rev l) <-> Weks l.
Proof.
  split.
  apply  Weks_Skew2.
  apply  Weks_Skew1.
Qed.
  (** *** Unicity *)

Lemma Weks_pos n l : Weks (n::l) -> 0 < n.
Proof.
  inv.
Qed.
Lemma Weks_inv n l : Weks (n::l) ->  Weks (l).
Proof.
  inv.
Qed.  
(** The key property : a canonical decomposition with [n] as
    largest factor cannot exceed [ones (S n)].
    Hence two decompositions with the same sum will have the
    same largest factors. *)
Lemma deb a n l: (ones a + sum_ones l) < ones n + 1  <-> ones n + (ones a + sum_ones l) < ones n + ones n + 1 .
Proof.
  omega.
Qed.

Lemma tr1 a n : ones a + ones a  <= ones n + ones n + 1 -> 
                ones a + ones a + 1 <= ones n + ones n + 1 + 1.
Proof.
  omega.
Qed.

  
Lemma uui a n :
  ones (S a) <= ones (S n) -> ones a + ones a  <= ones n + ones n + 1.
Proof.
  simpl in *.
  rewrite !Nat.add_0_r.
  
  omega.
Qed.

  
Lemma aux a b c:
  a < b -> c + a < c + b.
Proof.
  omega.
Qed.

Lemma aux2 n m:
  n <= m -> n + 1 <= m + 1.
Proof.
  omega.
Qed.
  
Lemma sum_ones_bound n l : 
  Weks (n::l) -> sum_ones (n::l) < ones (S n).
Proof.
  revert n.
  induction l.
  intros;simpl;auto.
  inv.
  rewrite <- !plus_n_O.
  rewrite <- plus_assoc.
  apply aux.  
  apply lt_le_trans with (ones (S a)).
  apply IHl;auto.
  induction n;simpl;auto.
  rewrite <- !plus_n_O in *.
  apply ones_le_mono in H2.
  apply aux2.
  simpl in *.
  rewrite <- !plus_n_O in *.
  omega.
Qed.


Lemma ones_pos_inv m :
  0 < ones m -> 0 < m.
Proof.
  induction m;auto.
Qed.
  
Lemma ones_lt_mono_inv n m : ones n < ones m -> n < m .
Proof.
  intros.
  destruct (le_lt_dec m n);auto.
  apply ones_le_mono in l;auto.
Qed.


Lemma  sum_equal a l l' :
  sum_ones (a :: l) = sum_ones (a :: l') -> sum_ones l = sum_ones l'.
Proof.
  inv.
Qed.  

  
Lemma decomp_unique_weks l l' : Weks l -> Weks l' ->
 sum_ones l = sum_ones l' -> l = l'.
Proof.
  revert l'.
  ind l;intros.
  destruct l';simpl in *;auto.
  inversion H0;subst;simpl in *;auto.
  apply ones_lt_mono in H3;simpl in H3;omega.
  apply ones_lt_mono in H3;simpl in H3;omega.
  apply ones_lt_mono in H4;simpl in H4;omega.
  destruct l';simpl in *;auto.
  inversion H;subst;simpl in *;auto.
  apply ones_lt_mono in H3;simpl in H3;omega.
  apply ones_lt_mono in H3;simpl in H3;omega.
  apply ones_lt_mono in H4;simpl in H4;omega.
  assert (a < S n).
  apply ones_lt_mono_inv.
  apply le_lt_trans with (ones n + sum_ones l').
  omega.
  apply sum_ones_bound;auto.
  assert (n < S a).
  apply ones_lt_mono_inv.
  apply le_lt_trans with (ones a + sum_ones l).
  omega.
  apply sum_ones_bound;auto.
  assert (a = n) by omega.
  subst.
  f_equal.
  apply IHl.
  apply Weks_inv in H;auto.
  apply Weks_inv in H0;auto.
  omega.
Qed.


Lemma rev_equal (l:list nat) (l':list nat) : l = l' -> (rev l) = (rev l').
Proof.
  inv.
Qed.
 
Lemma decomp_unique l l' : Skew l -> Skew  l' ->
 sum_ones l = sum_ones l' -> l = l'.
Proof.
  intros.
  rewrite <- (rev_involutive l) in *.
  rewrite <- (rev_involutive l') in *.
  apply Weks_Skew in H.
  apply Weks_Skew in H0.
  rewrite (sum_ones_rev (rev l)) in H1.
  rewrite (sum_ones_rev (rev l')) in H1.
  f_equal.
  apply decomp_unique_weks;auto.
Qed.
  
  

   
Lemma decomp_unique' l n :
  Skew l -> n = sum_ones l -> l = iter_next n.
Proof.
  intros.
  symmetry in H0.
  rewrite <- iter_next_sum in H0.
  apply decomp_unique;auto.
  apply iter_next_skew.
Qed.




(** *** Decomposition of predecessor *)

(** In the same spirit as [next], we could actually build
    the decomposition of [n-1] out of the decomposition of [n].
    Note that this function is meant to be used on canonical
    decomposition, [prev (0::l)] isn't supposed to occur, we can
    answer anything in this case, here [nil]. *)

Definition prev l :=
  match l with
  | 1::l => l
  | (S n)::l => n::n::l
  | _ => nil
  end.


Lemma prev_sum l : Skew l ->
 sum_ones (prev l) = pred (sum_ones l).
Proof.
  induction l;simpl;subst;auto.
  case a;simpl;auto.
  inv.
  intros.
  case n;simpl;auto.
Qed.  


Lemma prev_skew l : Skew l -> Skew (prev l).
Proof.
  induction l;simpl;auto.
  destruct a;simpl;auto.
  inv.
  destruct a;simpl;auto.
  destruct a;simpl;auto.
  apply Skew_inv in H;auto.
Qed.

(** And thanks to the unicity, we could easily prove results
    about the composition of [prev] and [next]. *)

Lemma prev_next l : Skew l -> prev (next l) = l.
Proof.
  inv.
  case Nat.eqb_spec;simpl;auto.
  case n;intros.
  omega.
  rewrite !e;auto.
Qed.
  
  
Lemma next_prev l : Skew l -> l<>nil -> next (prev l) = l.
Proof.
  inv.
  intros.
  destruct H0;auto.
  intros l.
  destruct n.
  intros;omega.
  destruct n.
  intros;simpl;auto.
  auto.
  simpl.
  case Nat.eqb_spec;auto.
  intros.
  omega.
  destruct n.
  omega.
  destruct n.
  intros;simpl.
  destruct l0;auto.
  case Nat.eqb_spec.
  intros.
  rewrite e in *.
  (** impossible cas l est ordonée donc par définition on utiliste 
le constructeur de Incr pour obtenir une contradiction *)
  inversion H1.
  omega.
  auto.
  simpl.
  case Nat.eqb_spec.
  auto.
  intros;omega.
Qed.
  
(** ** PART II : Some complements about Coq arithmetic and lists *)

(** *** An exact subtraction

   No rounding at zero with this one, but rather an output
   in [option nat]. Later, to prove things involving [sub_option],
   simply do a [case sub_option_spec]. *)

Fixpoint sub_option n m :=
  match n, m with
  | _, 0 => Some n
  | 0, _ => None
  | S n, S m => sub_option n m
  end.

Inductive SubOptionSpec (n m : nat) : option nat -> Prop :=
 | SubLe p : n = m + p -> SubOptionSpec n m (Some p)
 | SubLt : n < m -> SubOptionSpec n m None.
Hint Constructors SubOptionSpec.


Lemma ltsub n m : n < m -> sub_option n m = None.
Proof.
  revert m.
  ind n;intros.
  case H;auto.
  destruct m;simpl in *;auto.
  omega.
Qed.


Lemma subSome p :sub_option p 0 = Some p.
Proof.
  ind p.
Qed.
Lemma subSome0 m : sub_option m m = Some 0.
  ind m.
Qed.  


                 
Lemma gesub n p m : n = m + p -> sub_option n m = (Some p).
Proof.
  revert p m.
  ind n;destruct m;simpl in *;auto.
  intros;omega.
Qed.

Lemma ltadd m n:   m < n -> exists p, n = m + p.
Proof.
  intros.
  ind H.
  exists 1;auto.
  destruct IHle.
  exists (S x);omega.
Qed.

Lemma sub_option_spec n m : SubOptionSpec n m (sub_option n m).
Proof.
  revert m. ind n; destruct m; auto.
  destruct (IHn m); auto.
Qed.

(** *** Injectivity of list concatenation *)

Lemma eq_length0_empty {A} (l : list A):
  0 = length l -> [] = l.
Proof.
  destruct l;auto.
  discriminate.
Qed.
  
Lemma app_inv {A} (u u' v v' : list A) :
 length u = length u' ->u ++ v = u' ++ v' -> u = u' /\ v = v'.
Proof.
  revert u u' v v'.
  induction u; destruct u'; simpl; intros;auto.    
  discriminate;auto.
  discriminate;auto.
  inversion H0.
  inversion H.
  edestruct IHu;eauto.
  subst; auto.
Qed.

(** *** Access to the n-th element of a list

   This is a cleaner version of List.nth_error. *)

Fixpoint list_nth {A} (l:list A) i : option A :=
  match i,l with
    | 0,   x::_ => Some x
    | S j, _::l => list_nth l j
    | _, _ => None
  end.

Lemma list_nth_app_l {A} (l l':list A)(n:nat) : n < length l ->
  list_nth (l++l') n = list_nth l n.
Proof.
  revert l l' n.
  ind l;intros.
  omega.
  destruct n;simpl;auto.
Qed.

Lemma list_nth_app_r {A} (l l':list A)(n:nat) :
  list_nth (l++l') (length l + n) = list_nth l' n.
Proof.
  revert l l' n.
  ind l.
Qed.



(** ** PART III: Skew Lists *)

Section SkewList.
Parameter A:Type.

(** Skewlists are list of trees of elements.
    We want here to store [2^d-1] elements per tree of depth [d],
    so we put data at the nodes and not at the leaves.
    The value at the root node is the head of the skewlist, then
    comes the values in the left sub-tree, then the right sub-tree. *)

(** Perfect binary trees parametrized by their depth. *)

Inductive tree : nat -> Type :=
 | Leaf : tree 0
 | Node : forall {d}, A -> tree d -> tree d -> tree (S d).

(** A [dtree] is a pair of a depth and a tree of this depth. *)

Inductive dtree := Tree : forall {d}, tree d -> dtree.

(** The type of skewlists *)

Definition skewlist := list dtree.

(** The number of elements in a skewlist *)

Definition depth (t:dtree) := let (d,_) := t in d.
Definition skew_length l := sum_ones (map depth l).

(** The invariant we impose on skewlists to keep a nice complexity: *)

Definition SkewList l := Skew (map depth l).

Hint Unfold SkewList.

(** The empty skewlist *)

Definition empty : skewlist := nil.

Lemma empty_invariant : SkewList empty.
Proof.
  auto.
Qed.

(** *** Conversion from skewlist to regular list *)

Fixpoint tree_to_list {d} (t:tree d) :=
  match t with
  | Leaf => nil
  | Node _ a tl tr => a :: tree_to_list tl ++ tree_to_list tr
  end.

Fixpoint to_list l :=
  match l with
  | nil => nil
  | Tree _ t :: l => tree_to_list t ++ to_list l
  end.


(** *** Properties of length and size of trees and skewlists *)

Fixpoint size {d} (t:tree d) :=
  match t with
  | Leaf => 0
  | Node _ a tl tr => 1 + size tl + size tr
  end.

Lemma size_ones n (t : tree n) : size t = ones n.
Proof.
  ind t.
Qed.

Lemma length_tree_to_list d (t:tree d) :
 length (tree_to_list t) = size t.
Proof.
  ind t;auto.
  rewrite app_length;auto.
Qed.  


Lemma length_to_list l :
 length (to_list l) = skew_length l.
Proof.
  ind l.
  destruct a;simpl;auto.
  rewrite app_length;rewrite IHl.
  unfold skew_length;simpl;f_equal.
  rewrite length_tree_to_list;rewrite size_ones;auto.
Qed.
  
(** *** A adhoc induction principle on two trees of same depth *)

(** When you have two trees [(t1 t2 : tree n)], you cannot simply
    do [induction t1; destruct t2], Coq will most certainly
    complain about issues with dependent types. In this case,
    you will have to use the [tree_ind2] principle defined below.
    The details of how these things are built aren't important,
    just check the type of the obtained [tree_ind2] and compare
    it to the one of the automatically generated [tree_ind].
    NB: this part is inspired by P. Boutillier's Vector library.
*)

Definition case0 (t : tree 0) :
  forall (P : tree 0 -> Prop), P Leaf -> P t :=
  match t with
  | Leaf => fun P H => H
  | _ => tt
  end.

Definition caseS {n} (t : tree (S n)) :
  forall (P : tree (S n) -> Prop),
  (forall x t1 t2, P (Node x t1 t2)) -> P t :=
  match t with
  | Node _ x t1 t2 => fun P H => H x t1 t2
  | _ => tt
  end.

Definition tree_ind2 (P : forall {n}, tree n -> tree n -> Prop)
  (base : P Leaf Leaf)
  (rec : forall {n x tl1 tr1 y tl2 tr2},
    P tl1 tl2 -> P tr1 tr2 ->
    P (Node x tl1 tr1) (Node y tl2 tr2)) :=
  fix loop {n} (t1 : tree n) : forall t2 : tree n, P t1 t2 :=
  match t1 with
  | Leaf => fun t2 => case0 t2 _ base
  | Node _ x1 tl1 tr1 => fun t2 =>
    caseS t2 (P (Node x1 tl1 tr1))
     (fun x2 tl2 tr2 => rec (loop tl1 tl2) (loop tr1 tr2))
  end.
Check tree_ind2.

(** *** Unicity of the skewlist representation *)

Lemma tree_unique n (t t' : tree n) :
 tree_to_list t = tree_to_list t' -> t = t'.
Proof.
  induction n,t,t' using tree_ind2;auto.
  simpl.
  inv.
  apply app_inv in H2.
  destruct H2.
  apply IHt'1 in H0.
  apply IHt'2 in H1.
  rewrite H0.
  rewrite H1.
  auto.
  (** thanks to the unicity *)
  rewrite !length_tree_to_list.
  rewrite !size_ones.
  auto.
Qed.

Lemma length_tolist l l':
  to_list l = to_list l' -> length (to_list l) = length (to_list l').
Proof.
  inv.
Qed.

Lemma equalsum  n l : S (ones (S n) + sum_ones (l)) =  S (sum_ones (S n ::l)).
Proof.
  auto.
Qed.


Lemma sum_ones_bound_inv n l :
  Skew (n::l) ->  S (sum_ones (S n::l)) > ones (S n).
Proof.
  ind n.
Qed.


Lemma prof n (t t' : tree n) : t = t' -> Tree t = Tree t' .
Proof.
  inv.
Qed.
  
Lemma skewlist_unique l l' : SkewList l -> SkewList l' ->
 to_list l = to_list l' -> l = l'.
Proof.
  revert l'. 
  unfold SkewList.
  induction l;destruct l';auto.
  intros.
  inversion H0;subst;simpl;auto;destruct d;destruct t;simpl in *.
  omega.
  discriminate.
  omega.
  discriminate.
  intros.
  inversion H;subst;simpl;destruct a;destruct d;destruct t;
  auto;simpl in *;try solve [omega | discriminate].
  intros.
  assert ( (to_list (a::l)) = (to_list (d::l')) );auto.
  apply length_tolist in H1.
  simpl in *.
  destruct a;destruct d.
  
  rewrite !app_length in H1.
  rewrite !length_to_list in H1.
  unfold skew_length in H1.
  rewrite !length_tree_to_list in H1.
  rewrite !size_ones in  H1.
  simpl in *.

  apply (decomp_unique (d0 :: map depth l) (d :: map depth l') H H0) in H1.

  inversion H1;subst;simpl;auto.
  assert (Tree t=Tree t0).
  apply prof.
  simpl in *.
  apply app_inv in H2.
  destruct H2.
 
  apply (tree_unique d (t) (t0) );auto.

  rewrite !length_tree_to_list.
  rewrite !size_ones.
  auto.
  f_equal.
  auto.
  apply IHl.
  apply Skew_inv in H;auto.
  apply Skew_inv in H0;auto.
  
  simpl in *.
  apply app_inv in H2.
  destruct H2.
  auto.
  rewrite !length_tree_to_list.
  rewrite !size_ones.
  auto.
Qed.

  
(** *** Coercion from [tree d] to [tree d'] when [d=d']. *)

Definition coerc {d d'} : tree d -> d = d' -> tree d'.
Proof.
 destruct 2.
 trivial.
Defined.

Lemma coerc_to_list d d' (t:tree d) (e : d = d') :
 tree_to_list (coerc t e) = tree_to_list t.
Proof.
 now destruct e.
Qed.

(** *** cons *)

(** Insert an element into a skewlist.
    Constant cost (when ignoring the cost of comparison). *)

Definition leaf := Tree Leaf.

Definition singleton x := Tree (Node x Leaf Leaf).

Definition cons x l :=
  match l with
  | Tree d1 t1 :: Tree d2 t2 :: l' =>
    match eq_nat_dec d1 d2 with
    | left E => Tree (Node x (coerc t1 E) t2) :: l'
    | right _ => singleton x :: l
    end
  | _ => singleton x :: l
  end.

Lemma cons_next x l : map depth (cons x l) = next (map depth l).
Proof.
  ind l.
  destruct a;simpl;auto.
  destruct l;simpl;auto.
  destruct d0;simpl;auto.
  case (eq_nat_dec d d0);simpl in *;auto.
  case (Nat.eqb_spec).
  intros;subst;auto.
  intros;omega;auto.
  case (Nat.eqb_spec).
  intros;omega.
  auto.
Qed.


  
Lemma cons_invariant x l : SkewList l -> SkewList (cons x l).
Proof.
  unfold SkewList.
  rewrite cons_next.
  apply next_skew.
Qed.
  
  
Lemma cons_to_list x l : to_list (cons x l) = x :: to_list l.
Proof.
  ind l.
  destruct a;destruct l;simpl;auto.
  destruct d0;simpl;auto.
  case (eq_nat_dec d d0);auto.
  intros;simpl.
  rewrite coerc_to_list.
  rewrite app_assoc;auto.
Qed.

(** *** Conversion from a regular list to a skewlist

    We simply iterate [cons]. The cost is hence linear. *)

Definition from_list (l:list A) : skewlist := List.fold_right cons nil l.

Lemma cons_from_list x l : from_list (x::l) = cons x (from_list l).
  unfold from_list;simpl;auto.
Qed.

Lemma from_list_invariant l : SkewList (from_list l).
  unfold SkewList.
  ind l.
  rewrite cons_next.
  apply next_skew;auto.
Qed.
  
Lemma to_from l : to_list (from_list l) = l.
Proof.
  induction l;simpl;auto.
  rewrite cons_to_list.
  f_equal;auto.
Qed.


    
Lemma unique_from_to l : SkewList l -> l = from_list (to_list l).
Proof.
  intros.
  apply skewlist_unique;simpl;auto.
  apply from_list_invariant.
  rewrite to_from;auto.
Qed.
  



(** *** Decons : head element and rest of a skewlist, if any

    Constant cost. *)

Definition decons l :=
 match l with
 | Tree _ (Node 0 x _ _) :: l' => Some (x,l')
 | Tree _ (Node _ x tl tr) :: l' =>
   Some (x, Tree tl :: Tree tr :: l')
 | _ => None
 end.

Lemma decons_prev l x l':
 decons l = Some (x,l') -> map depth l' = prev (map depth l).
Proof.
  ind l;intros.
  discriminate.
  destruct a;simpl;auto.
  destruct t;simpl;auto.
  discriminate.
  destruct d;injection H;intros;subst;auto.
Qed.
  

Lemma decons_invariant x l l' :
 SkewList l -> decons l = Some (x,l') -> SkewList l'.
Proof.
  intros.
  apply decons_prev in H0.
  unfold SkewList;rewrite H0.
  apply prev_skew.
  unfold SkewList in H;auto.
Qed.

  
Lemma decons_none l : SkewList l -> (decons l = None <-> l = nil).
Proof.
  intros;split;intros.
  ind l.
  destruct a;simpl;auto.
  destruct t;simpl;auto.
  unfold SkewList in *;simpl in *.
  inversion H;omega.
  destruct d;discriminate.
  subst;auto.
Qed.

Lemma triv n (t1 t2 : tree n) : n=0 -> 
  tree_to_list t1 ++ tree_to_list t2 = [].
Proof.
  induction n,t1,t2 using tree_ind2;auto.
  simpl.
  intros;omega.
Qed.
  
Lemma decons_to_list x l l' :
 decons l = Some (x,l') -> to_list l = x :: to_list l'.
Proof.
  ind l;intros.
  discriminate.
  destruct a;simpl;auto.
  destruct t;simpl;auto.
  discriminate.
  destruct d;simpl;auto.
  injection H;intros;subst.
  f_equal;simpl in *.
  rewrite triv;simpl;auto.
  injection H;intros;subst.
  f_equal;simpl in *.
  rewrite app_assoc;reflexivity.
Qed.
  
Lemma decons_cons x l : SkewList l -> decons (cons x l) = Some (x,l).
Proof.
  intros;unfold SkewList in *.
  ind l.
  destruct a;simpl;auto.
  destruct l;simpl;auto.
  destruct d0;simpl;auto.
  case (eq_nat_dec d d0);simpl in *.
  inversion H;intros;subst.
  case H2.
  destruct d0;simpl;auto.
  intros;omega.
  intros;reflexivity.
Qed.
 
  
Lemma cons_decons x l l' :
 SkewList l -> decons l = Some (x,l') -> cons x l' = l.
Proof.
  intros;auto.
  assert (SkewList l);auto.
  assert (decons l = Some (x, l'));auto.
  apply decons_invariant in H0;auto.
  apply decons_to_list in H2.
  rewrite <- cons_to_list in H2.
  apply skewlist_unique;auto.
  apply cons_invariant;auto.
Qed.

(** *** Access to the n-th element of a skew list *)

(** n-th element of the tree t *)

Fixpoint nth_tree {d} (t : tree d) n :=
  match t with
  | Leaf => None
  | Node d x tl tr =>
    match n with
    | O => Some x
    | S n' =>
      match sub_option n' (ones d) with
      | None => nth_tree tl n'
      | Some n'' => nth_tree tr n''
      end
    end
  end.

(** n-th element of a skewlist l. *)

Fixpoint nth l n :=
  match l with
  | nil => None
  | Tree d t :: l =>
    match sub_option n (ones d) with
    | None => nth_tree t n
    | Some n' => nth l n'
    end
  end.

Lemma nth_tree_ok d (t : tree d) n :
  nth_tree t n = list_nth (tree_to_list t) n.
Proof.
  revert n.
  ind t.
  destruct n;simpl;auto.
  destruct n;simpl;auto.
  destruct (sub_option_spec n (ones d));subst.
  rewrite (IHt2 p).
  rewrite <- (size_ones d t1).
  rewrite <- length_tree_to_list.
  rewrite list_nth_app_r;auto.
  rewrite list_nth_app_l;auto.
  rewrite <- (size_ones d t1) in H.
  rewrite <- length_tree_to_list in H;auto.
Qed.

    
Lemma nth_ok l n : nth l n = list_nth (to_list l) n.
Proof.
  revert n.
  induction l.
  destruct n;simpl;auto.
  destruct a.
  destruct t.
  simpl.
  intros.
  case (sub_option_spec).
  intros.
  simpl in H.
  rewrite H.
  apply IHl.
  omega.
  simpl nth.
  intros.
  case (sub_option_spec).
  intros.
  assert (ones d + (ones d + 0) + 1 > 0).
  auto.
  case (zerop n) .
  destruct n.
  intros.
  omega.
  intros.
  omega.
  destruct n.
  intros.
  omega.
  simpl.
  rewrite <- plus_n_O in *.
  intros.
  rewrite <- (size_ones d t1) in H at 1.
  rewrite <- (size_ones d t2) in H at 1.
  rewrite <- length_tree_to_list in *.
  rewrite <- length_tree_to_list in *.
  assert (n =  length (tree_to_list t1) + length (tree_to_list t2)  + p) by omega.
  rewrite <- app_length in H1.
  rewrite H1.
  rewrite list_nth_app_r.
  auto.
  intros.
  destruct n.  
  simpl.
  auto.
  case (sub_option_spec).
  simpl.
  rewrite list_nth_app_l.
  intros.
  rewrite <- (size_ones d t1) in *.
  rewrite <- length_tree_to_list in *.
  rewrite H0.
  intros.
  rewrite list_nth_app_r.
  apply nth_tree_ok.
  rewrite <- (size_ones d t1) in H at 1.
  rewrite <- (size_ones d t2) in H at 1.
  rewrite <- length_tree_to_list in *.
  rewrite <- length_tree_to_list in *.
  rewrite <- plus_n_O in *.
  assert (n <  length (tree_to_list t1) + length (tree_to_list t2)  ) by omega.
  rewrite <- app_length in H0.
  auto.
  intros.
  simpl.
  rewrite list_nth_app_l.
  intros.
  rewrite <- (size_ones d t1) in H at 1.
  rewrite <- (size_ones d t2) in H at 1.
  rewrite <- plus_n_O in *.
  rewrite <- length_tree_to_list in H .
  assert ( n < length (tree_to_list t1) + size t2 ) by omega.
  rewrite list_nth_app_l.
  apply nth_tree_ok.
  rewrite <- (size_ones d t1) in H0 at 1.
  rewrite <- length_tree_to_list in H0 .
  auto.
  rewrite <- (size_ones d t1) in H at 1.
  rewrite <- (size_ones d t2) in H at 1.
  rewrite <- plus_n_O in *.
  rewrite <- !length_tree_to_list in H .
  assert ( n < length (tree_to_list t1) +  length (tree_to_list t2) ) by omega.
  rewrite <- app_length in H1.
  auto.
Qed.


(** In the "real life", all the arithmetical operations on the
  sizes will be done on machine integers, and hence have a
  constant cost (for instance [ones n = (1 << n) - 1]).
  In this situation, [cons] and [decons] have really a constant
  cost and [nth] has a logarithmic cost with respect to the
  number of elements in the skew list.

  In Coq, things are not so nice, since on [nat] all arithmetic
  operations are at least linear. We could at least define
  a notion of distance of elements in the skew list, and show
  that this distance is at most logarithmic. (TODO)
*)


(** Possible extensions :
  - a [set_nth] function, such that [set_nth l n x] creates a copy
    of the skewlist [l] where the n-th element is now replaced by [x].

  - a [drop] function, such that [drop k l] is the skewlist [l]
    with its first [k] elements removed. This could be done by
    repeating [k] times the [decons] function, but with a direct
    definition we could obtain a better complexity (logarithmic
    in the size of [l], when ignoring arithmetic ops).
*)

End SkewList.
