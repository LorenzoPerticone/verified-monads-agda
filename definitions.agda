module definitions where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

  open import utils

  -- Monoids
  data Monoid : Set → Set where
    monoid : {M : Set} → (e : M) →
             (_#_ : M → M → M) →
             ((x : M) → e # x ≡ x) →
             ((x : M) → x # e ≡ x) →
             ((x y z : M) → (x # y) # z ≡ x # (y # z)) →
             Monoid M

  unit : {M : Set} → {𝑀 : Monoid M} → M
  unit {𝑀 = monoid e _ _ _ _} = e

  -- Functors
  data Functor (F : Set → Set) : Set1 where
    functor : (map : {A B : Set} → (A → B) → F A → F B) →
              (mapReplace : {A B : Set} →
                            (f : A → B) → (g : A → B) →
                            ((x : A) → f x ≡ g x) →
                            (y : F A) → map f y ≡ map g y) →
              (ax1 : {A : Set} →
                     (x : F A) → map id x ≡ x) →
              (ax2 : {A B C : Set} →
                     (f : B → C) → (g : A → B) →
                     (x : F A) → map (f ∘ g) x ≡ (map f (map g x))) → 
              Functor F

  -- - Functor Utilities
  mapF : {A B : Set} → {F : Set → Set} →
         Functor F →
         (A → B) → F A → F B
  mapF (functor map _ _ _) = map

  -- - Identity Functor
  Id : Set → Set
  Id A = A

  𝟙 : Functor Id
  𝟙 = functor id (λ _ _ p x → p x) (λ _ → refl) (λ _ _ _ → refl)

  -- - Functor Composition
  infixl 20 _<>_
  _<>_ : (Set → Set) → (Set → Set) → (A : Set) → Set
  (F <> G) A = F (G A)

  mapComp : {F G : Set → Set} → {A B : Set} →
            (𝔽 : Functor F) → (𝔾 : Functor G) →
            (A → B) → (F <> G) A → (F <> G) B
  mapComp (functor map₁ _ _ _) (functor map₂ _ _ _) f x = map₁ (map₂ f) x

  mapReplaceComp : {F G : Set → Set} → {A B : Set} →
                   (𝔽 : Functor F) → (𝔾 : Functor G) →
                   (f : A → B) → (g : A → B) →
                   ((x : A) → f x ≡ g x) →
                   (y : (F <> G) A) →
                   mapComp 𝔽 𝔾 f y ≡ mapComp 𝔽 𝔾 g y
  mapReplaceComp (functor _ mapReplace₁ _ _) (functor map₂ mapReplace₂ _ _) f g p y =
    mapReplace₁ (map₂ f) (map₂ g) (mapReplace₂ f g p) y

  ax1Comp : {F G : Set → Set} → {A : Set} →
            (𝔽 : Functor F) → (𝔾 : Functor G) →
            (x : (F <> G) A) →
            mapComp 𝔽 𝔾 id x ≡ x
  ax1Comp (functor _ mapReplace₁ ax1₁ _) (functor map₂ _ ax1₂ _) x =
    trans (mapReplace₁ (map₂ id) id ax1₂ x) (ax1₁ x)

  ax2Comp : {F G : Set → Set} → {A B C : Set} →
            (𝔽 : Functor F) → (𝔾 : Functor G) →
            (f : B → C) → (g : A → B) →
            (x : (F <> G) A) →
            mapComp 𝔽 𝔾 (f ∘ g) x ≡ mapComp 𝔽 𝔾 f (mapComp 𝔽 𝔾 g x)
  ax2Comp (functor map₁ mapReplace₁ ax1₁ ax2₁) (functor map₂ mapReplace₂ ax1₂ ax2₂) f g x =
    trans (mapReplace₁ (map₂ (f ∘ g)) (map₂ f ∘ map₂ g) (ax2₂ f g) x) (ax2₁ (map₂ f) (map₂ g) x)

  infixl 20 _∙_
  _∙_ : {F G : Set → Set} →
        Functor F → Functor G → Functor (F <> G)
  𝔽 ∙ 𝔾 = functor (mapComp 𝔽 𝔾) (mapReplaceComp 𝔽 𝔾) (ax1Comp 𝔽 𝔾) (ax2Comp 𝔽 𝔾)
  
  -- Natural Transformations
  data _~>_ : {F G : Set → Set} → Functor F → Functor G → Set1 where
    NT : {F G : Set → Set} → {𝔽 : Functor F} → {𝔾 : Functor G} →
         (ϕ : {A : Set} →
              F A → G A) →
         (axNat : {A B : Set} →
                  (f : A → B) →
                  (x : F A) →
                  mapF 𝔾 f (ϕ x) ≡ ϕ (mapF 𝔽 f x)) →
         𝔽 ~> 𝔾

  -- - Utilities
  mor : {A : Set} → {F G : Set → Set} →
        {𝔽 : Functor F} → {𝔾 : Functor G} →
        𝔽 ~> 𝔾 →
        F A → G A
  mor (NT ϕ _) = ϕ

  -- - Identity Transformation
  𝕚𝕕 : {F : Set → Set} → {𝔽 : Functor F} → 𝔽 ~> 𝔽
  𝕚𝕕 {_} {𝔽} = NT id (λ _ _ → refl)

  -- - Vertical Composition
  morCompVert : {A : Set} → {F G H : Set → Set} →
                {𝔽 : Functor F} →
                {𝔾 : Functor G} →
                {ℍ : Functor H} →
                (𝔾 ~> ℍ) → (𝔽 ~> 𝔾) →
                F A → H A
  morCompVert (NT ϕ _) (NT ψ _) x = ϕ (ψ x)

  axCompVert : {A B : Set} → {F G H : Set → Set} →
               {𝔽 : Functor F} →
               {𝔾 : Functor G} →
               {ℍ : Functor H} →
               (ϕ : 𝔾 ~> ℍ) →
               (ψ : 𝔽 ~> 𝔾) →
               (f : A → B) →
               (x : F A) →
               mapF ℍ f (morCompVert ϕ ψ x) ≡
               morCompVert ϕ ψ (mapF 𝔽 f x)
  axCompVert (NT ϕ axNat₁) (NT ψ axNat₂) f x = 
    trans (axNat₁ f (ψ x)) (cong ϕ (axNat₂ f x))

  infixr 20 _⊙_
  _⊙_ : {F G H : Set → Set} →
        {𝔽 : Functor F} →
        {𝔾 : Functor G} →
        {ℍ : Functor H} →
        (𝔾 ~> ℍ) → (𝔽 ~> 𝔾) → (𝔽 ~> ℍ)
  ϕ ⊙ ψ = NT (morCompVert ϕ ψ) (axCompVert ϕ ψ)

  -- - Horizontal Composition
  morCompHor : {A : Set} → {F₁ F₂ G₁ G₂ : Set → Set} →
               {𝔽₁ : Functor F₁} → {𝔽₂ : Functor F₂} →
               {𝔾₁ : Functor G₁} → {𝔾₂ : Functor G₂} →
               (𝔽₁ ~> 𝔽₂) → (𝔾₁ ~> 𝔾₂) →
               (F₁ <> G₁) A → (F₂ <> G₂) A
  morCompHor {𝔽₁ = 𝔽₁} {𝔽₂ = 𝔽₂} (NT ϕ _) (NT ψ _) x =
    (ϕ (mapF 𝔽₁ ψ x))

  axCompHor : {F₁ F₂ G₁ G₂ : Set → Set} →
              {𝔽₁ : Functor F₁} → {𝔽₂ : Functor F₂} →
              {𝔾₁ : Functor G₁} → {𝔾₂ : Functor G₂} →
              (ϕ : 𝔽₁ ~> 𝔽₂) → (ψ : 𝔾₁ ~> 𝔾₂) →
              {A B : Set} → 
              (f : A → B) → (x : (F₁ <> G₁) A) →
              mapF (𝔽₂ ∙ 𝔾₂) f (morCompHor ϕ ψ x) ≡ morCompHor ϕ ψ (mapF (𝔽₁ ∙ 𝔾₁) f x)
  axCompHor {𝔽₁ = functor map₁₁ mapReplace₁₁ _ ax2₁₁} {𝔽₂ = functor _ _ _ _}
            {𝔾₁ = functor map₂₁ _ _ _} {𝔾₂ = functor map₂₂ _ _ _}
            (NT ϕ axNat₁) (NT ψ axNat₂) {_} {_} f x =
    let p1 = axNat₁ (map₂₂ f) (map₁₁ ψ x)
        p2 = cong ϕ (sym (ax2₁₁ (map₂₂ f) ψ x))
        p3 = cong ϕ (mapReplace₁₁ (map₂₂ f ∘ ψ) (ψ ∘ map₂₁ f) (axNat₂ f) x)
        p4 = cong ϕ (ax2₁₁ ψ (map₂₁ f) x)
    in (trans (trans p1 p2) (trans p3 p4))
              
  infixr 20 _⊗_
  _⊗_ : {F₁ F₂ G₁ G₂ : Set → Set} →
        {𝔽₁ : Functor F₁} → {𝔽₂ : Functor F₂} →
        {𝔾₁ : Functor G₁} → {𝔾₂ : Functor G₂} →
        (𝔽₁ ~> 𝔽₂) → (𝔾₁ ~> 𝔾₂) → ((𝔽₁ ∙ 𝔾₁) ~> (𝔽₂ ∙ 𝔾₂))
  ϕ ⊗ ψ = NT (morCompHor ϕ ψ) (axCompHor ϕ ψ)

  -- Left / Right whiskerings
  mapLeftWhisker : {A : Set} → {F G₁ G₂ : Set → Set} →
                   {𝔾₁ : Functor G₁} → {𝔾₂ : Functor G₂} →
                   (𝔽 : Functor F) → (𝔾₁ ~> 𝔾₂) →
                   (F <> G₁) A → (F <> G₂) A
  mapLeftWhisker (functor map _ _ _) (NT ϕ _) x = map ϕ x

  axLeftWhisker : {A B : Set} → {F G₁ G₂ : Set → Set} →
                  {𝔾₁ : Functor G₁} → {𝔾₂ : Functor G₂} →
                  (𝔽 : Functor F) → (ϕ : 𝔾₁ ~> 𝔾₂) →
                  (f : A → B) → (x : (F <> G₁) A) →
                  mapF (𝔽 ∙ 𝔾₂) f (mapLeftWhisker 𝔽 ϕ x) ≡ mapLeftWhisker 𝔽 ϕ (mapF (𝔽 ∙ 𝔾₁) f x)
  axLeftWhisker {𝔾₁ = functor map₁ _ _ _} {𝔾₂ = functor map₂ _ _ _}
                (functor map mapReplace _ ax2) (NT ϕ axNat) f x =
    let p1 = sym (ax2 (map₂ f) ϕ x)
        p2 = mapReplace ((map₂ f) ∘ ϕ) (ϕ ∘ (map₁ f)) (axNat f) x
        p3 = ax2 ϕ (map₁ f) x
    in trans p1 (trans p2 p3)

  infixl 20 _▷_
  _▷_ : {F G₁ G₂ : Set → Set} → {𝔾₁ : Functor G₁} → {𝔾₂ : Functor G₂} →
        (𝔽 : Functor F) → (𝔾₁ ~> 𝔾₂) →
        ((𝔽 ∙ 𝔾₁) ~> (𝔽 ∙ 𝔾₂))
  𝔽 ▷ ϕ = NT (mapLeftWhisker 𝔽 ϕ) (axLeftWhisker 𝔽 ϕ)

  mapRightWhisker : {A : Set} → {F₁ F₂ G : Set → Set} →
                    {𝔽₁ : Functor F₁} → {𝔽₂ : Functor F₂} →
                    (𝔽₁ ~> 𝔽₂) → (𝔾 : Functor G) →
                    (F₁ <> G) A → (F₂ <> G) A
  mapRightWhisker (NT ϕ _) (_) x = ϕ x

  axRightWhisker : {A B : Set} → {F₁ F₂ G : Set → Set} →
                   {𝔽₁ : Functor F₁} → {𝔽₂ : Functor F₂} →
                   (ϕ : 𝔽₁ ~> 𝔽₂) → (𝔾 : Functor G) →
                   (f : A → B) → (x : (F₁ <> G) A) →
                   mapF (𝔽₂ ∙ 𝔾) f (mapRightWhisker ϕ 𝔾 x) ≡ mapRightWhisker ϕ 𝔾 (mapF (𝔽₁ ∙ 𝔾) f x)
  axRightWhisker {𝔽₁ = functor _ _ _ _} {𝔽₂ = functor _ _ _ _}
                 (NT ϕ axNat) (functor map _ _ _) f x =
    axNat (map f) x

  infixr 20 _◁_
  _◁_ : {F₁ F₂ G : Set → Set} → {𝔽₁ : Functor F₁} → {𝔽₂ : Functor F₂} →
        (𝔽₁ ~> 𝔽₂) → (𝔾 : Functor G) →
        ((𝔽₁ ∙ 𝔾) ~> (𝔽₂ ∙ 𝔾))
  ϕ ◁ 𝔾 = NT (mapRightWhisker ϕ 𝔾) (axRightWhisker ϕ 𝔾)

  -- Left and Right unitors for functor composition
  mapULeft : {A : Set} → {F : Set → Set} →
             {𝔽 : Functor F} →
             (Id <> F) A → F A
  mapULeft x = x

  axULeft : {A B : Set} → {F : Set → Set} →
            {𝔽 : Functor F} →
            (f : A → B) →
            (x : (Id <> F) A) →
            mapF 𝔽 f (mapULeft {𝔽 = 𝔽} x) ≡ mapULeft {𝔽 = 𝔽} (mapF (𝟙 ∙ 𝔽) f x)
  axULeft {𝔽 = functor map _ _ _} f x = refl
  
  𝕦Left : {F : Set → Set} → {𝔽 : Functor F} →
          ((𝟙 ∙ 𝔽) ~> 𝔽)
  𝕦Left {𝔽 = 𝔽} = NT (mapULeft {𝔽 = 𝔽}) (axULeft {𝔽 = 𝔽})

  mapURight : {A : Set} → {F : Set → Set} →
              {𝔽 : Functor F} →
              (F <> Id) A → F A
  mapURight x = x

  axURight : {A B : Set} → {F : Set → Set} →
             {𝔽 : Functor F} →
             (f : A → B) →
             (x : (F <> Id) A) →
             mapF 𝔽 f (mapURight {𝔽 = 𝔽} x) ≡ mapURight {𝔽 = 𝔽} (mapF (𝔽 ∙ 𝟙) f x)
  axURight {𝔽 = functor _ _ _ _} f x = refl

  𝕦Right : {F : Set → Set} → {𝔽 : Functor F} →
           ((𝔽 ∙ 𝟙) ~> 𝔽)
  𝕦Right {𝔽 = 𝔽} = NT (mapURight {𝔽 = 𝔽}) (axURight {𝔽 = 𝔽})

  -- Associator for functor composition (useful?)
  mapAssoc : {A : Set} → {F G H : Set → Set} → {𝔽 : Functor F} → {𝔾 : Functor G} → {ℍ : Functor H} →
             ((F <> G) <> H) A → (F <> (G <> H)) A
  mapAssoc x = x

  axAssoc : {A B : Set} → {F G H : Set → Set} → {𝔽 : Functor F} → {𝔾 : Functor G} → {ℍ : Functor H} →
            (f : A → B) → (x : ((F <> G) <> H) A) →
            mapF (𝔽 ∙ (𝔾 ∙ ℍ)) f (mapAssoc {𝔽 = 𝔽} {𝔾 = 𝔾} {ℍ = ℍ} x) ≡
            mapAssoc {𝔽 = 𝔽} {𝔾 = 𝔾} {ℍ = ℍ} (mapF ((𝔽 ∙ 𝔾) ∙ ℍ) f x)
  axAssoc {𝔽 = functor _ _ _ _} {𝔾 = functor _ _ _ _} {ℍ = functor _ _ _ _} f x = refl

  assoc : {F G H : Set → Set} → {𝔽 : Functor F} → {𝔾 : Functor G} → {ℍ : Functor H} →
          (((𝔽 ∙ 𝔾) ∙ ℍ) ~> (𝔽 ∙ (𝔾 ∙ ℍ)))
  assoc {𝔽 = 𝔽} {𝔾 = 𝔾} {ℍ = ℍ} = NT (mapAssoc {𝔽 = 𝔽} {𝔾 = 𝔾} {ℍ = ℍ}) (axAssoc {𝔽 = 𝔽} {𝔾 = 𝔾} {ℍ = ℍ})

  -- Monads
  data Monad (M : Set → Set) : Set1 where
    monad : (𝕄 : Functor M) →
            (η : 𝟙 ~> 𝕄) →
            (μ : (𝕄 ∙ 𝕄) ~> 𝕄) →
            (axLeftUnit : {A : Set} → (x : (Id <> M) A) →
                          mor (μ ⊙ (η ◁ 𝕄)) x ≡ mor {𝔽 = 𝟙 ∙ 𝕄} {𝔾 = 𝕄} 𝕦Left x) →
            (axRightUnit : {A : Set} → (x : (M <> Id) A) →
                           mor (μ ⊙ (𝕄 ▷ η)) x ≡ mor {𝔽 = 𝕄 ∙ 𝟙} {𝔾 = 𝕄} 𝕦Right x) →
            (axAssoc : {A : Set} → (x : ((M <> M) <> M) A) →
                       mor (μ ⊙ (μ ◁ 𝕄)) x ≡ mor (μ ⊙ (𝕄 ▷ μ)) x) →
            Monad M

  -- - Identity Monad
  axLeftUnitId : {A : Set} → (x : (Id <> Id) A) →
                 mor {𝔾 = 𝟙} (𝕦Left ⊙ (𝕚𝕕 ◁ 𝟙)) x ≡ mor {𝔾 = 𝟙} 𝕦Left x
  axLeftUnitId x = refl

  axRightUnitId : {A : Set} → (x : (Id <> Id) A) →
                  mor {𝔾 = 𝟙} (𝕦Left ⊙ (𝟙 ▷ 𝕚𝕕)) x ≡ mor {𝔾 = 𝟙} 𝕦Right x
  axRightUnitId x = refl

  axAssocId : {A : Set} → (x : ((Id <> Id) <> Id) A) →
              mor {𝔾 = 𝟙} (𝕦Left ⊙ (𝕦Left ◁ 𝟙)) x ≡
              mor {𝔾 = 𝟙} (𝕦Left ⊙ (𝟙 ▷ 𝕦Left)) x
  axAssocId x = refl

  𝕀d : Monad Id
  𝕀d = monad 𝟙 𝕚𝕕 𝕦Left axLeftUnitId axRightUnitId axAssocId
