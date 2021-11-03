module writer where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils
  open import definitions

  data _×_ (A B : Set) : Set where
    <_,_> : A → B → A × B

  fst : {A B : Set} → A × B → A
  fst < x , y > = x
  snd : {A B : Set} → A × B → B
  snd < x , y > = y

  Writer : Set → Set → Set
  Writer E A = E × A

  mapWriter : {A B E : Set} → (A → B) → Writer E A → Writer E B
  mapWriter f < x , y > = < x , f y >

  mapReplaceWriter : {A B E : Set} → (f : A → B) → (g : A → B) →
                     ((x : A) → f x ≡ g x) → (y : Writer E A) →
                     mapWriter f y ≡ mapWriter g y
  mapReplaceWriter f g p < x , y > = cong (< x ,_>) (p y)

  ax1Writer : {A E : Set} → (x : Writer E A) →
              mapWriter {E = E} id x ≡ x
  ax1Writer < x , y > = refl

  ax2Writer : {A B C E : Set} → (f : B → C) → (g : A → B) → (x : Writer E A) →
              mapWriter (f ∘ g) x ≡ mapWriter f (mapWriter g x)
  ax2Writer f g < x , y > = refl

  𝑊riter : (E : Set) → Functor (Writer E)
  𝑊riter E = functor mapWriter mapReplaceWriter ax1Writer ax2Writer

  unitWriterMorp : {A E : Set} → {𝐸 : Monoid E} → Id A → Writer E A
  unitWriterMorp {E = E} {𝐸 = 𝐸} x = < unit {M = E} {𝑀 = 𝐸} , x >

  unitWriterAxNat : {A B E : Set} → {𝐸 : Monoid E} →
                    (f : A → B) → (x : Id A) →
                    mapWriter {E = E} f (unitWriterMorp {E = E} {𝐸 = 𝐸} x) ≡
                    unitWriterMorp {E = E} {𝐸 = 𝐸} (id f x)
  unitWriterAxNat f x = refl

  unitWriter : {E : Set} → {𝐸 : Monoid E} → 𝟙 ~> 𝑊riter E
  unitWriter {𝐸 = 𝐸} = NT (unitWriterMorp {𝐸 = 𝐸}) (unitWriterAxNat {𝐸 = 𝐸})

  multWriterMorp : {A E : Set} → {𝐸 : Monoid E} →
                   (Writer E <> Writer E) A → Writer E A
  multWriterMorp {𝐸 = monoid _ _#_ _ _ _} < x , < y , z > > = < x # y , z >

  multWriterAxNat : {A B E : Set} → {𝐸 : Monoid E} →
                    (f : A → B) → (x : (Writer E <> Writer E) A) →
                    mapWriter f (multWriterMorp {𝐸 = 𝐸} x) ≡
                    multWriterMorp {𝐸 = 𝐸} (mapWriter (mapWriter f) x)
  multWriterAxNat {𝐸 = monoid _ _#_ _ _ _} f < x , < y , z > > = refl

  multWriter : {E : Set} → {𝐸 : Monoid E} →
               (𝑊riter E ∙ 𝑊riter E) ~> 𝑊riter E
  multWriter {𝐸 = 𝐸} = NT (multWriterMorp {𝐸 = 𝐸}) (multWriterAxNat {𝐸 = 𝐸})

  axUnitLeftWriter : {A E : Set} → {𝐸 : Monoid E} →
                     (x : (Id <> Writer E) A) →
                     mor (multWriter {𝐸 = 𝐸} ⊙ (unitWriter {𝐸 = 𝐸} ◁ 𝑊riter E)) x ≡
                     mor {𝔾 = 𝑊riter E} 𝕦Left x
  axUnitLeftWriter {𝐸 = monoid e _#_ pleft _ _} < x , y > = cong (<_, y >) (pleft x)

  axUnitRightWriter : {A E : Set} → {𝐸 : Monoid E} →
                      (x : (Writer E <> Id) A) →
                      mor (multWriter {𝐸 = 𝐸} ⊙ (𝑊riter E ▷ unitWriter {𝐸 = 𝐸})) x ≡
                      mor {𝔾 = 𝑊riter E} 𝕦Right x
  axUnitRightWriter {𝐸 = monoid e _#_ _ pright _} < x , y > = cong (<_, y >) (pright x)

  axAssocWriter : {A E : Set} → {𝐸 : Monoid E} →
                  (x : (Writer E <> Writer E <> Writer E) A) →
                  multWriterMorp {𝐸 = 𝐸} (multWriterMorp {𝐸 = 𝐸} x) ≡
                  multWriterMorp {𝐸 = 𝐸} (mapWriter (multWriterMorp {𝐸 = 𝐸}) x)
  axAssocWriter {𝐸 = monoid e _#_ _ _ ptrans} < x , < y , < z , w > > > = cong (<_, w >) (ptrans x y z)

  𝕎riter : (E : Set) → {𝐸 : Monoid E} → Monad (Writer E)
  𝕎riter E {𝐸 = 𝐸} = monad (𝑊riter E) (unitWriter {𝐸 = 𝐸}) (multWriter {𝐸 = 𝐸})
                            axUnitLeftWriter axUnitRightWriter axAssocWriter
