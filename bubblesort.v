(* begin hide *)
Require Import Arith List Recdef.
(* end hide *)

(** * Descrição do Projeto *)     

(** A prova da correção de um algoritmo de ordenação consiste de duas etapas. Inicialmente, provaremos que o algoritmo efetivamente ordena os elementos da lista dada como argumento, e em seguida precisamos mostrar que a lista de saída é uma permutação da lista dada como entrada. *)

(** ** Parte 1 *)
(** Inicialmente, definimos indutivamente o predicado [sorted], que nos permite provar se uma lista dada como argumento está ordenada: *)

Inductive sorted :list nat -> Prop :=
  | nil_sorted : sorted nil
  | one_sorted: forall n:nat, sorted (n :: nil)
  | all_sorted : forall (x y: nat) (l:list nat), sorted (y :: l) -> x <= y -> sorted (x :: y :: l).

(** O predicado [sorted] possui três construtores, a saber [nil_sorted], [one_sorted] and [all_sorted]. Os dois primeiros construtores são axiomas que afirmam que a lista vazia e que listas unitárias estão ordenadas: 

 %\begin{mathpar} \inferrule*[Right={$(nil\_sorted)$}]{~}{sorted\ nil} \and
  \inferrule*[Right={$(one\_sorted)$}]{~}{\forall n, sorted (n :: nil)} \end{mathpar}%

O terceiro construtor, i.e. [all_sorted] estabelece as condições para que uma lista com pelo menos dois elementos esteja ordenada. Assim, quaisquer que sejam os elementos $x$ e $y$, e a lista $l$, temos:

%\begin{mathpar} \inferrule*[Right={$(all\_sorted)$}]{sorted (y :: l) \and x \leq y}{sorted (x :: y :: l)}\end{mathpar}%

Ou seja, para provarmos que a lista $x :: y :: l$ está ordenada, precisamos provar que $x \leq y$ e que a lista $y :: l$ também está ordenada.
 *)

(** No lema a seguir, mostramos como provar que se uma lista não vazia está ordenada, então sua cauda também está ordenada. Observe que $l$ é uma sublista de $a::l$ e compare este fato com a questão 1. *)

Lemma tail_sorted: forall l a, sorted (a :: l) -> sorted l. 
Proof.
  intro l. (** %\comm{ Este comando introduz uma constante no contexto da prova, e é sempre utilizado quando temos quantificação universal ou implicação no consequente. Este processo é conhecido como  skolemização. Na prática de provas em Matemática, isto  corresponde a dizer "seja {\color{black}$l$} uma lista qualquer".}% *)

  case l. (** %\comm{ Este comando faz uma análise de casos sobre $l$. Temos então dois casos a considerar: }% *)
  
  - intros a H.  (** %\comm{ No primeiro subcaso, a lista $l$ é a lista vazia. Sejam $a$ um natural e $H$ a hipótese de que a lista $a :: nil$ está ordenada. }% *)
    
    apply nil_sorted.  (** %\comm{ Precisamos provar que a lista vazia está ordenada. Para isto basta aplicarmos o axioma $nil\_sorted$. }%*)
    
  - intros n l' a H.  (** %\comm{ No caso indutivo, sejam $n$ um natural, $l'$ uma lista, $a$ um natural e $H$ a hipótese de que a lista $a :: n :: l'$ está  ordenada. Precisamos provar que a lista $n :: l'$ está  ordenada. }%*)
    
    inversion H; subst.  (** %\comm{ Observe que o fato de  $sorted (a :: n :: l')$ (hipótese $H$) significa que $a \leq n$ e $sorted (n :: l')$ de acordo com a regra $all_sorted$. O comando {\tt inversion} gera as condições que permitem construir uma hipótese, e é normalmente combinada com a tática $subst$ que faz substituições e elimina as igualdades geradas pelo comando $inversion$. }%*)
    
    assumption.  (** %\comm{ Observe que uma das hipóteses geradas pelo comando anterior é exatamente o que queremos provar. O comando {\tt assumption} verifica que o  objetivo atual corresponde a uma das hipóteses. }% *)
    
Qed.  

(** ** Questão 1: *)
(** A primeira questão deste projeto consiste em provar que se temos uma lista com pelo menos dois elementos $a1::a2::l$ e removemos o segundo elemento, a lista obtida $a1::l$ (que não é uma sublista da lista original!) também está ordenada. Se você precisar utilizar a transitividade de $\leq$, use o lema [Nat.le_trans]. *)

Lemma remove_sorted: forall l a1 a2, sorted (a1 :: a2 :: l) -> sorted (a1 :: l).
Proof.
  Admitted. (* Substitua esta linha com a sua prova *)

(** O algoritmo [bubblesort] é baseado na função [bubble] que percorre a lista dada como argumento comparando seus elementos consecutivos: *)
(* printing *)
(** printing <=? $\leq ?$ *)

Function bubble (l: list nat) {measure length} :=
  match l with
  | h1 :: h2 :: tl =>
    if h1 <=? h2
    then  h1 :: (bubble (h2 :: tl))
    else h2 :: (bubble (h1 :: tl))
    | _ => l
  end.
(* begin hide *)
Proof.
  - intros.
    simpl.
    apply Nat.lt_succ_diag_r.
  - intros.
    simpl.
    apply Nat.lt_succ_diag_r.
Defined.
(* end hide *)

(** Mais precisamente, a função [bubble] recebe uma lista $l$ de
números naturais como argumento, e é definida recursivamente. A
recursão é baseada no tamanho da lista, e daí a necessidade do
parâmetro [measure] %{\tt length}%. Observe que se a lista dada como
entrada possui dois ou mais elementos então os dois primeiros
elementos são comparados, e se necessário, suas posições são
trocadas. O processo continua com a comparação do segundo e terceiro
elementos, e assim até que o penúltimo e o último elementos sejam
comparados. Quando a lista é vazia ou unitária, a função [bubble] não
faz nada. Por exemplo, aplicando a função [bubble] à lista
$4::3::2::1::nil$ obtemos como resultado a lista $3::2::1::4::nil$
porque inicialmente 4 é comparado com 3, e neste caso o 3 é movido
para fora da recursão e o processo continua como $3::$([bubble]\
$4::2::1::nil$). No passo seguinte, o 4 é comparado com o 2 e temos
$3::2::$([bubble]\ $4::1::nil$), e finalmente, 4 é comparado com o 1 e
obtemos a lista $3::2::1::4::nil$. *)

(** ** Questão 2: *)
(** A segunda questão a ser resolvida neste projeto consiste em provar que a função [bubble] não faz nada em listas ordenadas: *)

Lemma bubble_sorted: forall l, sorted l -> bubble l = l.
Proof.
    Admitted. (* Substitua esta linha com a sua prova *)

(** O algoritmo [bubblesort] é definido recursivamente como abaixo. A palavra reservada [Fixpoint] é utilizada para definir funções recursivas (simples) enquanto que [Function] usada na definição de [bubble] é utilizada para definir funções recursivas mais sofisticadas, cuja métrica que garante a sua boa definição precisa ser fornecida explicitamente: *)

Fixpoint bubblesort (l: list nat) :=
  match l with
  | nil => nil
  | h :: tl => bubble (h :: bubblesort tl)
  end.

(** O predicado $le\_all$, definido a seguir, recebe um natural $n$ e uma lista $l$ como argumentos, e a fórmula $le\_all\ n\ l$ possui uma prova quando $n$ é menor ou igual a todos os elementos da lista $l$. Escreveremos $n \leq\! *\ l$ ao invés de $le\_all\ n\ l$. *)

Definition le_all x l := Forall (fun y => x <= y) l.
(* begin hide *)
Infix "<=*" := le_all (at level 70, no associativity).
(* end hide *)

(** O predicado [Forall] acima é  definido indutivamente pelas seguintes regras:
    
%\begin{mathpar} \inferrule*[Right={$(Forall\_nil)$}]{~}{Forall\ P\ nil} \end{mathpar}%

%\begin{mathpar} \inferrule*[Right={$(Forall\_cons)$}]{P\ x \and Forall\ P\ l}{Forall\ P\ (x::l)} \end{mathpar}%

Assim, dada uma propriedade $P$ sobre elementos de um dado tipo $A$, $Forall\ P\ l$ consiste em uma prova de que todos os elementos de $l$ satisfazem a propriedade $P$. De fato, a regra $Forall\_nil$ consiste no axioma que diz que, por vacuidade, todos os elementos da lista vazia satisfazem a propriedade $P$. Já a regra $Forall\_cons$ fornece uma prova de que a lista $x::l$ satisfaz a propriedade $P$ a partir das provas de que $x$ satisfaz $P$, e de que todos os elementos de $l$ também satisfazem $P$.
 
 A seguir provaremos duas propriedades envolvendo o predicado $le\_all$. Nosso primeiro exemplo, consiste em mostrar que se a lista $a::l$ está ordenada então $a$ é menor ou igual do que qualquer elemento de $l$. *)

(* printing *)
(** printing <=* $\leq\! *$ *)
Lemma sorted_le_all: forall l a, sorted(a :: l) -> a <=* l.
Proof.
  induction l.  (** %\comm{ Esta prova é feita por indução na estrutura da lista $l$. Teremos então dois casos a considerar: o caso em que $l$ é a lista vazia, e o caso em que $l$ não é vazia. }%*)
  
  - intros a H.  (** %\comm{ A base de indução consiste no caso em que a lista $l$ é a lista vazia. Sejam então $a$ um número natural, e $H$ a hipótese de que a lista $a::nil$ está ordenada. Precisamos provar que o natural $a$ é menor ou igual a todos os elementos da lista vazia. }%*)
    
    apply Forall_nil. (** %\comm{ Mas como comentado anteriormente, este caso consiste na aplicação do axioma $Forall\_nil$. }%*)
    
  - intros a' H. (** %\comm{ No caso em que a lista não é vazia, digamos $a::l$, sejam $a'$ um número natural e $H$ a hipótese de que a lista $a'::a::l$ está ordenada. Precisamos provar que $a'$ é menor ou igual a todos os elementos de $a::l$. }%*)
    
    inversion H; subst. (** %\comm{ Como $a'::a::l$ está ordenada, então pela definição de $sorted$ temos que $a' \leq a$ e que $a::l$ está ordenada. A tática $inversion$ deriva para cada construtor possível de $sorted\ (a' :: a :: l)$ as condições necessárias para a sua prova. Neste caso, o único construtor possível é $all\_sorted$ que nos dá como hipóteses que $a' \leq a$ e que a lista $a::l$ está ordenada. }%*)
    
    apply Forall_cons. (* %\comm{ Para provarmos que  $a' <=* a :: l$ utilizamos a regra $Forall_cons$, e portanto teremos dois subcasos: }% *)
    
    + assumption. (** %\comm{ Inicialmente precisamos mostrar que $a' \leq a$, mas esta foi uma das hipóteses geradas por $inversion\ H$. }%*)
      
    + apply IHl. (** %\comm{ Agora no passo indutivo, temos por hipótese de indução que, para qualquer natural $a$, se a lista $a::l$ está ordenada então $a <=* l$. Podemos aplicar a hipótese de indução instanciando $a$ com $a'$ e então temos que provar que a lista $a'::l$ está ordenada.  }%*)
      
      apply remove_sorted in H; assumption. (** %\comm{ Como a hipótese $H$ nos diz que a lista $a'::a::l$ está ordenada, podemos concluir esta prova usando o lema provado na questão 1. }%*)
      
Qed.

(** ** Questão 3 *)
(** Agora sejam $a$ um natural e $l$ uma lista ordenada. Prove que se $a$ é menor ou igual do que todos os elementos de $l$ então a lista $a::l$ está ordenada. *)

Lemma le_all_sorted: forall l a, a <=* l -> sorted l -> sorted (a :: l).
Proof.
    Admitted. (* Substitua esta linha com a sua prova *)

(** A seguir provaremos que se o natural $a$ é menor ou igual do que todos os elementos da lista $l$ então $a$ é menor ou igual do que todos os elementos da lista $bubble\ l$. *)

Lemma le_all_bubble: forall l a, a <=* l -> a <=* bubble l.
Proof.
  intros l a H. (** %\comm{ Sejam $l$ uma lista de naturais, $a$ um natural e $H$ a hipótese de que $a$ é menor ou igual a todos os elementos de $l$. }%*)
  
functional induction (bubble l).  (** %\comm{ É natural tentarmos iniciar esta prova fazendo indução na estrutura de $l$, mas nossa hipótese de indução não será expressiva suficiente porque a função [bubble] não é definida sobre a estrutura de $l$, mas sobre o comprimento de $l$. O princípio de indução baseado no comprimento de $l$ é obtido via o comando $functional\ induction\ (bubble\ l)$, e temos 3 casos a considerar. Suponha que $l$ tem a forma $h1::h2::tl$: }%*)
  
  - inversion H; subst.  (** %\comm{ Quando $h1 \leq h2$, precisamos provar que $a \leq\! * h1::  bubble (h2::tl)$. Como $l$ tem a forma $h1::h2::tl$, a hípotese $H$ nos diz que $a \leq\! * h1::h2::tl$ de onde obtemos que $a \leq h1$ e que $a \leq\! (h2::tl)$ via o comando $inversion\ H$. }%*)
    
    apply Forall_cons. (** %\comm{ Neste passo dividimos a prova de $a \leq\! * h1::  bubble (h2::tl)$ em duas subprovas de acordo com o construtor $Forall_cons$ como visto anteriormente:  }% *)
    
    + assumption.  (* %\comm{ Inicialmente precisamos provar que $a \leq h1$, mas esta é uma das nossas hipóteses. }%*)

    + apply IHl0; assumption. (** %\comm{ Agora precisamos provar que $a \leq\! * bubble (h2::tl)$ que pode ser provado pela hipótese de indução desde que $a \leq (h2::tl)$, mas este fato é uma das nossas hipóteses. }%*)
      
  - inversion H; subst. (** %\comm{ Quando $h2 < h1$, precisamos provar que $a \leq\!* h2:: bubble (h1::tl)$. Da hipótese $H$ obtemos novamente que $a \leq h1$ e $a \leq\! (h2::tl)$. }%*)
   
    apply Forall_cons. (** %\comm{ A prova de $a \leq\!* h2:: bubble (h1::tl)$ pode ser dividida em duas subprovas de acordo com o construtor $Forall_cons$: }%*)
    
    + inversion H3; subst; assumption. (** %\comm{ A primeira subprova consiste em mostrar que $a \leq h2$ e pode ser obtida a partir da inversão da hipótese $a \leq\! (h2::tl)$. }%*)
      
    + apply IHl0. (** %\comm{ A segunda subprova consiste em mostrar que  $a \leq\!* bubble (h1::tl)$. Para isto utilizamos a hipótese de indução. }%*)
      
      inversion H3; subst. (** %\comm{ Ao aplicarmos a hipótese de indução reduzimos nosso problema a mostrar que $a \leq\!* h1::tl$. }%*)
      
      apply Forall_cons; assumption. (** %\comm{ A prova de $a \leq\!* h1::tl$ é dividida nas provas de que $a \leq h1$ e $a \leq\!* tl$ que são hipóteses obtidas de duas inversões anteriores. }%*)
      
  - assumption.  (** %\comm{ Por fim, o terceiro caso da definição da função $bubble$ retorna a própria lista $l$, e portanto este é um caso trivial. }%*)
    
Qed.  

(** ** Questão 4 *)
(** Mostre que se $l$ é uma lista ordenada então a lista $bubble\ (a::l)$ também está ordenada, qualquer que seja o natural $a$. Alguns resultados, além dos já provados anteriormente podem ser úteis nesta prova como, por exemplo [Nat.leb_le], [Nat.leb_nle], [Nat.nle_gt] e [Nat.lt_le_incl]. *)

Lemma bubble_sorted_sorted: forall l a, sorted l -> sorted (bubble (a :: l)).
Proof.
    Admitted. (* Substitua esta linha com a sua prova *)

(** Neste momento podemos provar que $bubblesort\ l$ retorna uma lista ordenada, qualquer que seja a lista $l$: *)

Theorem bubblesort_sorts: forall l, sorted (bubblesort l).
Proof.
  induction l.
  - simpl.
    apply nil_sorted.
  - simpl.
    apply bubble_sorted_sorted.
    assumption.
Qed.

(** ** Parte 2 *)
(** A segunda parte da prova da correção do algoritmo $bubblesort$ consiste em mostrar que a lista de saída é uma permutação da lista de entrada. *)

(** A permutação de listas é definida indutivamente como a seguir: *)

Inductive perm: list nat -> list nat -> Prop :=
| perm_refl: forall l, perm l l
| perm_hd: forall x l l', perm l l' -> perm (x::l) (x::l')
| perm_swap: forall x y l l', perm l l' -> perm (x::y::l) (y::x::l')
| perm_trans: forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

(**  Nesta definição, o construtor [perm_refl] corresponde ao axioma que estabelece que uma lista é permutação dela mesma:

     %\begin{mathpar} \inferrule*[Right={$(perm\_refl)$}]{~}{perm\ l\ l} \end{mathpar}%
 *)

(** Já o construtor [perm_hd] estabelece que, se a lista $l$ é uma permutação da lista $l'$ então a lista com cabeça $x$ e cauda $l$ é uma permutação da lista que tem cabeça $x$ e cauda $l'$:

%\begin{mathpar} \inferrule*[Right={$(perm\_hd)$}]{perm\ l\ l'}{perm\ (x :: l)\ (x :: l')} \end{mathpar}%
  *)

(** O construtor [perm_swap] nos permite provar que listas que tenham os dois primeiros elementos permutados sejam permutações uma da outra desde que as sublistas correspondentes a partir do terceiro elemento sejam permutação uma da outra: 

%\begin{mathpar} \inferrule*[Right={$(perm\_swap)$}]{perm\ l\ l'}{perm\ (x :: y :: l)\ (y :: x :: l')} \end{mathpar}%

E por fim, o construtor [perm_trans] estabelece que a permutação de listas é transitiva.

%\begin{mathpar} \inferrule*[Right={$(perm\_trans)$}]{perm\ l1\ l2\and perm\ l2\ l3}{perm\ l1\ l3} \end{mathpar}%
  *)

(** ** Questão 5 *)
(** Prove que a função $bubble$ gera uma permutação da lista de entrada: *)

Lemma bubble_is_perm: forall l, perm (bubble l) l.
Proof.
    Admitted. (* Substitua esta linha com a sua prova *)

(** ** Questão 6 *)
(** Mostre que se a lista $l$ é uma permutação da lista $l'$ então $bubble\ (a::l)$ é uma permutação de $(a::l')$. *)

Lemma bubble_is_perm': forall l l' a, perm l l' -> perm (bubble (a::l)) (a :: l').
Proof.
    Admitted. (* Substitua esta linha com a sua prova *)

(** Agora podemos concluir a segunda parte da formalização com a prova de que $bubblesort$ gera uma permutação da lista de entrada. *)

Theorem bubblesort_is_perm: forall l, perm (bubblesort l) l.
Proof.
  induction l.
  - simpl.
    apply perm_refl.
  - simpl.
    apply bubble_is_perm'.
    assumption.
Qed.

(** O resultado principal, que caracteriza a correção do algoritmo de ordenação $bubblesort$, é  dado a seguir: *)

Proposition bubblesort_is_correct: forall l, perm (bubblesort l) l /\ sorted (bubblesort l).
Proof.
  intro l; split.
  - apply bubblesort_is_perm.
  - apply bubblesort_sorts.
Qed. 


(* begin hide *)

(** ** Extração de código *)


Require Extraction.

(** As opções de linguagens são: Ocaml, Haskell e Scheme. *)
Extraction Language Ocaml.

(** Extração apenas da função [bubblesort]. *) Extraction bubblesort.

(** Extração do programa inteiro. *) Recursive Extraction bubblesort.

(** Extração para um arquivo. *) Extraction "bubblesort" bubblesort.

(* end hide *)
