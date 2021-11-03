module continuation where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils
  open import definitions

  Cont : Set → Set → Set
  Cont E A = (A → E) → E

  ev : {A E : Set} → (A → E) → Cont E A → E
  ev f ϕ = ϕ f

  mapCont : {A B E : Set} → (A → B) → Cont E A → Cont E B
  mapCont f ϕ = λ g → ϕ (g ∘ f)

  mapReplaceCont : {A B E : Set} →
                   (f : A → B) → (g : A → B) →
                   ((x : A) → f x ≡ g x) →
                   (y : Cont E A) →
                   mapCont f y ≡ mapCont g y
  mapReplaceCont f g p x = {!!}

  ax1Cont : {A E : Set} → (x : Cont E A) →
            mapCont id x ≡ x
  ax1Cont x = refl

  ax2Cont : {A B C E : Set} → (f : B → C) → (g : A → B) →
            (x : Cont E A) →
            mapCont (f ∘ g) x ≡ mapCont f (mapCont g x)
  ax2Cont f g x = refl

  𝐶ont : (E : Set) → Functor (Cont E)
  𝐶ont E = functor mapCont mapReplaceCont ax1Cont ax2Cont

  unitContMorp : {A E : Set} → Id A → Cont E A
  unitContMorp x = λ f → f x

  unitContAxNat : {A B E : Set} → (f : A → B) → (x : Id A) →
                  mapCont {E = E} f (unitContMorp x) ≡ unitContMorp (id f x)
  unitContAxNat f x = refl

  unitCont : {E : Set} → 𝟙 ~> 𝐶ont E
  unitCont = NT unitContMorp unitContAxNat

  multContMorp : {A E : Set} → (Cont E <> Cont E) A → Cont E A
  multContMorp ϕ = λ f → ϕ (ev f)

  multCompAxNat : {A B E : Set} → (f : A → B) →
                  (x : (Cont E <> Cont E) A) →
                  mapCont f (multContMorp x) ≡ multContMorp (mapCont (mapCont f) x)
  multCompAxNat f x = refl

  multCont : {E : Set} → (𝐶ont E ∙ 𝐶ont E) ~> (𝐶ont E)
  multCont = NT multContMorp multCompAxNat

  axUnitLeftCont : {A E : Set} → (x : (Id <> Cont E) A) →
                   mor (multCont ⊙ (unitCont ◁ 𝐶ont E)) x ≡ mor {𝔾 = 𝐶ont E} 𝕦Left x
  axUnitLeftCont x = refl

  axUnitRightCont : {A E : Set} → (x : (Cont E <> Id) A) →
                    mor (multCont ⊙ (𝐶ont E ▷ unitCont)) x ≡ mor {𝔾 = 𝐶ont E} 𝕦Right x
  axUnitRightCont x = refl

  axAssocCont : {A E : Set} → (x : (Cont E <> Cont E <> Cont E) A) →
                multContMorp (multContMorp x) ≡ multContMorp (mapCont multContMorp x)
  axAssocCont x = refl

  ℂont : (E : Set) → Monad (Cont E)
  ℂont E = monad (𝐶ont E) unitCont multCont axUnitLeftCont axUnitRightCont axAssocCont
