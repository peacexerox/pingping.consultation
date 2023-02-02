
(** Helpers *)
Require Import String.

Inductive tag(T:Type): T->string->string->string->Prop:=
| str_(t:T)(n:string)(ts:string)(s':string): tag T t ts n s'
.
Arguments tag {T}%type_scope _ _ _ _.
Open Scope string_scope.

Definition generalize(T:Type)(t:T)(r:string)(ts:string)(s':string)(e0: tag t r ts s'): { s:string & T }.
  constructor.
  pose (String (Ascii.ascii_of_nat 10) EmptyString ++ "(** " ++ s' ++ " *) " ++
          String (Ascii.ascii_of_nat 10) EmptyString
          ++           String (Ascii.ascii_of_nat 10) EmptyString
          ++  "Parameter " ++ r ++ ": " ++ ts ++ ". "
          ++ String (Ascii.ascii_of_nat 10) EmptyString ++ "Parameter " ++ r ++ "': tag " ++ r ++ " """ ++ r ++ """ """ ++ ts ++ """ """  ++ s' ++ """%string. "
          ++ String (Ascii.ascii_of_nat 10) EmptyString ++ "(** End of segment *) "
          ++ String (Ascii.ascii_of_nat 10) EmptyString ++ "(** " ++ s' ++ " *)").
  exact s. 
  exact t.
Defined.
Arguments generalize {T}%type_scope {_} {_}%string_scope {_}%string_scope {_}%string_scope _.



Definition generalize_qa(T:Type)(t:T)(r:string)(ts:string)(s':string)(e0: tag t r ts s'): { s:string*string & T }.
  constructor.
  pose s' as question.
  pose (String (Ascii.ascii_of_nat 10) EmptyString ++ "(** " ++ s' ++ " *) " ++
          String (Ascii.ascii_of_nat 10) EmptyString
          ++           String (Ascii.ascii_of_nat 10) EmptyString
          ++  "Parameter " ++ r ++ ": " ++ ts ++ ". "
          ++ String (Ascii.ascii_of_nat 10) EmptyString ++ "Parameter " ++ r ++ "': tag " ++ r ++ " """ ++ r ++ """ """ ++ ts ++ """ """  ++ s' ++ """%string. "
          ++ String (Ascii.ascii_of_nat 10) EmptyString ++ "(** End of segment *) "
          ++ String (Ascii.ascii_of_nat 10) EmptyString ++ "(** " ++ s' ++ " *)") as answer.
  exact (pair question answer).
  exact t.
Defined.
Arguments generalize_qa {T}%type_scope {_} {_}%string_scope {_}%string_scope {_}%string_scope _.


Definition explain(T:Type)(t:T)(r:string)(ts:string)(s':string)(e0: tag t r ts s'): string.
  pose s' as explain.
  exact explain.
Defined.
Arguments explain {T}%type_scope {_} {_}%string_scope {_}%string_scope {_}%string_scope _.
Definition conclusion(T:Type)(t:T)(r:string)(ts:string)(s':string)(e0: tag t r ts s'): string.
  pose ("Conclusion is: " ++ s') as conclusion.
  exact conclusion.
Defined.
Arguments conclusion {T}%type_scope {_} {_}%string_scope {_}%string_scope {_}%string_scope _.
Definition premise(T:Type)(t:T)(r:string)(ts:string)(s':string)(e0: tag t r ts s'): string.
  pose ("Premise : " ++ s') as premise.
  exact premise.
Defined.
Arguments premise {T}%type_scope {_} {_}%string_scope {_}%string_scope {_}%string_scope _.



Definition Men:=Set. 
Parameter mortal: (Men->Prop). 
Parameter mortal': tag mortal "mortal" "Men->Prop" "[mortal] is an attributes that applies to [men]"%string.
Compute ( generalize mortal').
Compute ( generalize_qa mortal').



Axiom all_men_mortal: forall m: Men, mortal m.
Parameter all_men_mortal':  tag all_men_mortal "all_men_mortal" " forall m: Men, mortal m"
                              "All men is mortal. "%string.

Compute (generalize all_men_mortal').

Axiom socrates: Men.
Parameter socrates': tag socrates "socrates" "Men" "Socrates is a Man. "%string. 


Definition socrates_is_mortal_claim := mortal socrates.
Parameter socrates_is_mortal' : tag socrates_is_mortal_claim "socrates_is_mortal" "mortal socrates" "Socrates is mortal."%string.

Definition socrates_is_mortal : socrates_is_mortal_claim.
  pose all_men_mortal as cc.
  pose (premise all_men_mortal') as cc1; cbv in cc1.
  
  pose socrates as sc.
  pose (premise socrates') as socrates1; cbv in socrates1.
  pose (conclusion socrates_is_mortal') as concl1; cbv in concl1.
  apply cc.
  Show Proof.
Qed.

Print socrates_is_mortal.

