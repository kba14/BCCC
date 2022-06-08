Class Category := cat_mk {
  Obj : Type;

  uHom := Type : Type;

  Hom : Obj -> Obj -> uHom;

  Id : forall x, Hom x x;

  Dom {x y} (f: Hom x y) := x;

  CoDom {x y} (f: Hom x y) := y;

  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;

  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;

}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Context {C : Category}.

Class CartClosed := {

(* terminal *)

  Terminal_obj : Obj;

  Terminal_mor : forall {x}, x → Terminal_obj;
 
  unique_terminal : forall {x} (f : x → Terminal_obj), f = Terminal_mor;

(* initial *)

  Initial_obj : Obj;

  Initial_mor : forall {x}, Initial_obj → x;

  unique_initial : forall {x} (f : Initial_obj → x), f = Initial_mor;

(* szorzat *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  pr_1 {x y} : (Prod_obj x y) → x;
  pr_2 {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (pr_1 ∘ (Prod_mor f g) = f) /\ (pr_2 ∘ (Prod_mor f g) = g);
    
  prod_eq : forall {x y z} (g : x → Prod_obj y z),
    Prod_mor (pr_1 ∘ g) (pr_2 ∘ g) = g;

(* exponenciális *)

  Exp_obj : Obj -> Obj -> Obj;

  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Exp_app ∘ (Prod_mor ((Lam g) ∘ pr_1) ((Id y) ∘ pr_2)) = g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (h ∘ pr_1) ((Id y) ∘ pr_2))) = h

}.


Notation "⊤" := (Terminal_obj) (at level 40, no
associativity) : type_scope.

Notation "〇" := (Initial_obj) (at level 40, no associativity) : type_scope.

Notation "f '∏' g" := (Prod_mor f g) (at level 40, no associativity) : type_scope.

Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) :
type_scope. 

Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) :
type_scope.

Context {CC : CartClosed}.

Theorem id_11 : forall x y (f : (Hom x y)), f = (Compose f (Id x)).
Proof.
intros.
assert (H: f ∘ Id x = f).
apply id_1.
congruence.
Qed.

Theorem unique_prod : forall x y z (f1 : x → y) (f2 : x → z) (g : x → Prod_obj y z),
    ((pr_1 ∘ g) = f1) /\ ((pr_2 ∘ g) = f2) ->  Prod_mor f1 f2 = g.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H1; rewrite <- H2.
apply prod_eq.
Qed.


Theorem compos_prod : forall x y z w (f : w → y ) (g : w → z ) (h : x → w),
  (f ∘ h) ∏ (g ∘ h) = ( f ∏ g ) ∘ h.
Proof.
intros.
apply unique_prod.
split.
assert (H:pr_1 ∘ (f ∏ g ∘ h) = pr_1 ∘ (f ∏ g) ∘ h).
apply assoc.
rewrite H.
assert (K:pr_1 ∘ (f ∏ g)=f).
apply prod_ax.
rewrite K.
auto.
assert (H: pr_2 ∘ ((f ∏ g) ∘ h) = pr_2 ∘ (f ∏ g) ∘ h).
apply assoc.
rewrite H.
assert (K:pr_2 ∘ (f ∏ g)=g).
apply prod_ax.
rewrite K.
auto.
Qed.


Theorem dist_prod : forall x y z w (f : Hom z (Exp_obj y x)) (g : Hom w z), ((f ∘ pr_1) ∏ ((Id x) ∘ pr_2)) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2)) = ((f ∘ g) ∘ pr_1) ∏ ((Id x) ∘ pr_2).
Proof.
intros.
assert (H1: ((f ∘ pr_1) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))) ∏ (((Id x) ∘ pr_2) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))) = (f ∘ pr_1) ∏ ((Id x) ∘ pr_2) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2)) ).
apply compos_prod with (f := f ∘ pr_1) (g := (Id x) ∘ pr_2) (h := (g ∘ pr_1) ∏ ((Id x) ∘ pr_2)).
rewrite <- H1.
assert (H2: f ∘ (pr_1 ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))) = (f ∘ pr_1) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))  ).
apply assoc with (f0 := f) (g0 := pr_1) (h := (g ∘ pr_1) ∏ ((Id x) ∘ pr_2)).
rewrite <- H2.
assert (H3: pr_1 ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2)) = g ∘ pr_1).
apply prod_ax with (f0 := g ∘ pr_1) (g0 := (Id x) ∘ pr_2).
rewrite H3.
assert (H4: (Id x) ∘ (pr_2 ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))) = ((Id x) ∘ pr_2) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))   ).
apply assoc with (f0 := Id x) (g0 := pr_2) (h := (g ∘ pr_1) ∏ ((Id x) ∘ pr_2)).
rewrite <- H4.
assert (H5: pr_2 ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2)) = (Id x) ∘ pr_2 ).
apply prod_ax with (f0 := g ∘ pr_1) (g0 := (Id x) ∘ pr_2).
rewrite H5.
assert (H61: (Id x) ∘ ((Id x) ∘ @pr_2 CC w x) = (Id x) ∘ pr_2   ).
apply id_2.
assert (H62: f ∘ (g ∘ @pr_1 CC w x) = (f ∘ g) ∘ pr_1 ).
apply assoc.
rewrite <- H62.
rewrite H61.
auto.
Qed.

Theorem distributive_law : forall (x y z w : Obj) (f: Hom (Prod_obj z x) y) (g: Hom w z), (Lam f) ∘ g = Lam (f ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))).
Proof.
intros.
assert (H1: Exp_app ∘ (((Lam f ∘ g) ∘ pr_1) ∏ (Id x ∘ pr_2)) = f ∘ ((g ∘ pr_1) ∏ (Id x ∘ pr_2)) ).
assert (H2: ((Lam f ∘ pr_1) ∏ (Id x ∘ pr_2)) ∘ ((g ∘ pr_1) ∏ (Id x ∘ pr_2)) = ((Lam f ∘ g) ∘ pr_1) ∏ (Id x ∘ pr_2) ).
apply dist_prod with (f := Lam f) (g := g).
rewrite <- H2.
assert (H3: Exp_app ∘ ((((Lam f) ∘ pr_1) ∏ ((Id x) ∘ pr_2)) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2))) = Exp_app ∘ (((Lam f) ∘ pr_1) ∏ ((Id x) ∘ pr_2)) ∘ ((g ∘ pr_1) ∏ ((Id x) ∘ pr_2)) ).
apply assoc.
rewrite H3.
assert (H4: Exp_app ∘ (((Lam f) ∘ pr_1) ∏ ((Id x) ∘ pr_2)) = f ).
apply exp_ax.
rewrite H4.
auto.
assert (K1: Lam (Exp_app ∘ ((((Lam f) ∘ g) ∘ pr_1) ∏ ((Id x) ∘ pr_2))) = (Lam f) ∘ g ).
apply unique_exp with (h := (Lam f) ∘ g).
congruence.
Qed.

Theorem prlemma : forall (x y : Obj), Prod_mor pr_1 pr_2 = Id (x × y).
Proof.
intros.
apply unique_prod.
split.
apply id_1.
apply id_1.
Qed.

Definition inbijection x y := exists (f: x -> y), (forall x y, f x = f y -> x = y) /\ (forall y : y, exists x, f x = y).

Theorem Currying : forall x y z, inbijection (Hom (z × x) y) (Hom z (y e↑ x)).
Proof.
intros.
unfold inbijection.
exists (fun f => Lam f).
split.
intros.
assert (H1: Exp_app ∘ (Prod_mor ((Lam x0) ∘ pr_1) ((Id x) ∘ pr_2)) = x0).
apply exp_ax.
assert (H2: Exp_app ∘ (Prod_mor ((Lam y0) ∘ pr_1) ((Id x) ∘ pr_2)) = y0).
apply exp_ax.
rewrite <- H in H2.
congruence.
intros.
exists (Exp_app ∘ (Prod_mor (y0 ∘ pr_1) ((Id x) ∘ pr_2))).
apply unique_exp.
Qed.

Theorem homlemma : forall (x y z : Obj), inbijection (Hom (x × y) z) (Hom (y × x) z).
Proof.
intros.
unfold inbijection.
exists (fun f => f ∘ (pr_2 ∏ pr_1) ).
split.
intros.
assert (H1 : x0 = (x0 ∘ (pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1))).
assert (A: x0 ∘ ((pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1)) = x0 ∘ (pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1)  ).
apply assoc with (f := x0) (g := pr_2 ∏ pr_1) (h := pr_2 ∏ pr_1).
rewrite <- A.
assert (C: (pr_2 ∘ (pr_2 ∏ pr_1)) ∏ (pr_1 ∘ (pr_2 ∏ pr_1)) = (@pr_2 CC y x ∏ pr_1) ∘ (pr_2 ∏ pr_1) ).
apply compos_prod with (f := pr_2) (g := pr_1) (h := pr_2 ∏ pr_1).
rewrite <- C.
assert (P1: @pr_2 CC y x ∘ (pr_2 ∏ pr_1) = pr_1).
apply prod_ax.
assert (P2: @pr_1 CC y x ∘ (pr_2 ∏ pr_1) = pr_2).
apply prod_ax.
rewrite P1.
rewrite P2.
assert (I: pr_1 ∏ pr_2 = Id (x × y) ).
apply prlemma with (x := x) (y := y).
rewrite I.
apply id_11 with (f := x0).
rewrite H1.
rewrite H.
assert (H2: y0 = ((y0 ∘ (pr_2 ∏ pr_1)) ∘ (pr_2 ∏ pr_1)) ).
assert (A: y0 ∘ ((pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1)) = y0 ∘ (pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1)  ).
apply assoc with (f := y0) (g := pr_2 ∏ pr_1) (h := pr_2 ∏ pr_1).
rewrite <- A.
assert (C: (pr_2 ∘ (pr_2 ∏ pr_1)) ∏ (pr_1 ∘ (pr_2 ∏ pr_1)) = (@pr_2 CC y x ∏ pr_1) ∘ (pr_2 ∏ pr_1) ).
apply compos_prod with (f := pr_2) (g := pr_1) (h := pr_2 ∏ pr_1).
rewrite <- C.
assert (P1: @pr_2 CC y x ∘ (pr_2 ∏ pr_1) = pr_1).
apply prod_ax.
assert (P2: @pr_1 CC y x ∘ (pr_2 ∏ pr_1) = pr_2).
apply prod_ax.
rewrite P1.
rewrite P2.
assert (I: pr_1 ∏ pr_2 = Id (x × y) ).
apply prlemma with (x := x) (y := y).
rewrite I.
apply id_11 with (f := y0).
rewrite <- H2.
auto.

intros.
exists (y0 ∘ (pr_2 ∏ pr_1) ).
assert (A: y0 ∘ ((pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1)) = y0 ∘ (pr_2 ∏ pr_1) ∘ (pr_2 ∏ pr_1)  ).
apply assoc with (f := y0) (g := pr_2 ∏ pr_1) (h := pr_2 ∏ pr_1).
rewrite <- A.
assert (C: (pr_2 ∘ (pr_2 ∏ pr_1)) ∏ (pr_1 ∘ (pr_2 ∏ pr_1)) = (@pr_2 CC x y ∏ pr_1) ∘ (pr_2 ∏ pr_1) ).
apply compos_prod with (f := pr_2) (g := pr_1) (h := pr_2 ∏ pr_1).
rewrite <- C.
assert (P1: @pr_2 CC x y ∘ (pr_2 ∏ pr_1) = pr_1).
apply prod_ax.
assert (P2: @pr_1 CC x y ∘ (pr_2 ∏ pr_1) = pr_2).
apply prod_ax.
rewrite P1.
rewrite P2.
assert (I: pr_1 ∏ pr_2 = Id (y × x) ).
apply prlemma with (x := y) (y := x).
rewrite I.
apply id_1 with (f := y0).
Qed.

Definition Singleton (H : uHom) := exists x : H, forall y : H, y = x.

Theorem initialHom : forall Y, Singleton (Hom Initial_obj Y).
Proof.
intros.
unfold Singleton.
exists Initial_mor.
intros.
apply unique_initial.
Qed.

Theorem inbij_singl : forall (x y : uHom), ((inbijection x y) /\ Singleton y) -> Singleton x.
Proof.
intros.
destruct H as [H1 H2].
unfold Singleton.
unfold Singleton in H2.
unfold inbijection in H1.
destruct H1 as (f, H1).
destruct H2 as (z, H2).
destruct H1 as (H11, H12).
specialize (H12 z).
destruct H12 as (x0, H12).
exists (x0).
intros.
assert (E: f y0 = f x0).
rewrite H2.
specialize (H2 (f y0)).
rewrite H2.
auto.
specialize (H11 y0 x0).
auto.
Qed.

Theorem singletonlemma_1 : forall x, Singleton (Hom (Prod_obj (Exp_obj x Initial_obj) Initial_obj) x).
Proof.
intros.
assert (B1: inbijection (Hom (Prod_obj (Exp_obj x Initial_obj) Initial_obj) x) (Hom (Prod_obj Initial_obj (Exp_obj x Initial_obj)) x) ).
apply homlemma.
assert (B2: inbijection (Hom (Prod_obj Initial_obj (Exp_obj x Initial_obj)) x) ((〇) → (x e↑ (x e↑ (〇))))  ).
apply Currying.
assert (S: Singleton ((〇) → (x e↑ (x e↑ (〇)))) ).
apply initialHom.
assert (S1: Singleton (((〇) × (x e↑ (〇))) → x)).
apply inbij_singl with (y := (〇) → (x e↑ (x e↑ (〇)))).
split.
apply B2.
apply initialHom.
apply inbij_singl with (y := (((〇) × (x e↑ (〇))) → x)).
split.
apply B1.
apply S1.
Qed.

Theorem singletonlemma_2 : forall x, Singleton (Hom (Prod_obj (Exp_obj x Initial_obj) Initial_obj) (Prod_obj (Exp_obj x Initial_obj) Initial_obj) ).
Proof.
intros.
assert (B1: inbijection (Hom (Prod_obj (Exp_obj x Initial_obj) Initial_obj) (Prod_obj (Exp_obj x Initial_obj) Initial_obj)) (Hom (Prod_obj Initial_obj (Exp_obj x Initial_obj)) (Prod_obj (Exp_obj x Initial_obj) Initial_obj))  ).
apply homlemma.
assert (B2: inbijection (((〇) × (x e↑ (〇))) → ((x e↑ (〇)) × (〇))) ((〇) → ((x e↑ (〇)) × (〇)) e↑ (x e↑ (〇))) ).
apply Currying.
assert (S: Singleton ((〇) → (((x e↑ (〇)) × (〇)) e↑ (x e↑ (〇)))) ).
apply initialHom.
assert (S1: Singleton (((〇) × (x e↑ (〇))) → ((x e↑ (〇)) × (〇))) ).
apply inbij_singl with (y := ((〇) → (((x e↑ (〇)) × (〇)) e↑ (x e↑ (〇)))) ).
split.
apply B2.
apply initialHom.
apply inbij_singl with (y := (((〇) × (x e↑ (〇))) → ((x e↑ (〇)) × (〇))) ).
split.
apply B1.
apply S1.
Qed.

Definition isomorph x y := exists (i : x → y) (j : y → x), i ∘ j = Id y /\ j ∘ i = Id x.

Notation "x '≅' y" := (isomorph x y) (at level 40, left associativity) :
type_scope.

Theorem Nullad_x_egyenlő_egy : forall X, (X e↑ 〇) ≅ ⊤.
Proof.
intros.
unfold isomorph.
exists (@Terminal_mor CC (X e↑ 〇)).
exists (Lam ((@Initial_mor CC X) ∘ (@pr_2 CC Terminal_obj Initial_obj))).
split.
assert (I: (Id Terminal_obj) = (@Terminal_mor CC Terminal_obj)).
apply unique_terminal.
rewrite I.
apply unique_terminal.

assert (D: (Lam ((@Initial_mor CC X) ∘ (@pr_2 CC Terminal_obj Initial_obj))) ∘ @Terminal_mor CC (Exp_obj X Initial_obj) = Lam ((Initial_mor ∘ pr_2) ∘ ((Terminal_mor ∘ pr_1) ∏ ((Id Initial_obj) ∘ pr_2)))).
apply distributive_law.
rewrite D.
assert (E: (@Initial_mor CC X ∘ @pr_2 CC Terminal_obj Initial_obj) ∘ ((@Terminal_mor CC (Exp_obj X Initial_obj) ∘ pr_1) ∏ ((Id Initial_obj) ∘ pr_2)) = Exp_app ).
assert (E1: Singleton (Hom (Prod_obj (Exp_obj X Initial_obj) Initial_obj) X)  ).
apply singletonlemma_1.
unfold Singleton in E1.
destruct E1 as (x, E1).
congruence.
rewrite E.
assert (I: Exp_app = Exp_app ∘ Id ((X e↑ (〇)) × (〇)) ).
apply id_11.
rewrite I.
assert (U: Id ((X e↑ (〇)) × (〇)) = ((Id (X e↑ (〇))) ∘ pr_1) ∏ ((Id (Initial_obj)) ∘ pr_2)  ).
assert (U1: Singleton (Hom (Prod_obj (Exp_obj X Initial_obj) Initial_obj) (Prod_obj (Exp_obj X Initial_obj) Initial_obj))   ).
apply singletonlemma_2.
unfold Singleton in U1.
destruct U1 as (x, U1).
congruence.
rewrite U.
apply unique_exp.
Qed. 




