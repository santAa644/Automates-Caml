(*
l
let rec ecritAux lang = match lang with
	|(Concaténation (a, b)) -> ((ecritAux a) ^ "" ^ (ecritAux b))
	|(Union (a, b)) -> (" " ^ (ecritAux a) ^ "U" ^ (ecritAux b))
	|(Etoilage a) -> (" " ^ (ecritAux a) ^ "*")
	|(Seul a) -> let rec aux l = match l with [] -> "" |(lettre h)::q -> h ^ (aux q) in aux (lettreList_of_mot a);;
let rec ecritAuxParenthese lang = match lang with
	|(Concaténation (a, b)) -> ("(" ^ (ecritAuxParenthese a) ^ "." ^ (ecritAuxParenthese b) ^ ")")
	|(Union (a, b)) -> ("(" ^ (ecritAuxParenthese a) ^ "U" ^ (ecritAuxParenthese b) ^ ")")
	|(Etoilage a) -> ("(" ^ (ecritAuxParenthese a) ^ ")*")
	|(Seul a) -> let rec aux l = match l with [] -> "e" |(lettre h)::q -> h ^ (aux q) in aux (lettreList_of_mot a);;

let ConcaténationBis (a, b) = match (a, b) with ((Seul (mot [])), a) -> a |(a, (Seul (mot []))) -> a |(a, b) -> (Concaténation (a, b));;

let rec epuration str = if (string_length str > 0) then if (str.[0] <> `.`) then str else
	let n = string_length str in
	let res = ref "" in
	for i=1 to n-1 do
		res := !res ^ (string_of_char str.[i]);
	done;
	!res else "";;

let ecrit lang = epuration (ecritAux lang);;
let ecritParenthese lang = epuration (ecritAuxParenthese lang);;

let creation strBis = 
	let str = strBis ^ " " in
	let n = string_length str in
	(*Faudrait gerer les parentheses : une LIFO*)
	let L = ref (Seul mot_vide) in
	for i=1 to n-1 do
		let tmp = str.[i] in
		if (tmp = `*`) then L := (ConcaténationBis (!L, (Etoilage (Seul (mot [(lettre (string_of_char (str.[i-1])))])))));
		if (tmp = `U`) then L := (ConcaténationBis (!L, (Union ((Seul (mot [(lettre (string_of_char (str.[i-1])))])), (Seul (mot [(lettre (string_of_char (str.[i+1])))]))))));
		if (i>0 && tmp <> `*` && str.[i-1] <> `*` && tmp <> `U` && str.[i-1] <> `U`) then L := (ConcaténationBis (!L, (Seul (mot [(lettre (string_of_char str.[i-1]))]))));
	done;
	!L;;

(*Si jamais on dispose de deux automates qui reconnaissent deux languages : on peut faire la concaténation, l'U, l'inter, l'un moins l'autre par ex*)
(*On suppose qu'ils sont deterministes*)
let creationConcatenation auto1 auto2 =
	let creationSlash n = let tmp = ref "" in for i=1 to n do tmp := !tmp ^ "/" done; !tmp in
	let rec aux1 l = match l with [] -> [] |(etat a)::q -> (etat (a ^ "/")) :: (aux1 q) in
	let rec aux2 l = match l with [] -> [] |(etat b)::q -> (etat ("/" ^ b)) :: (aux2 q) in
	let rec auxaux l n1 n2 = match l with [] -> [] |(etat a)::q -> (etat ((creationSlash n1) ^ a ^ (creationSlash n2))) :: (auxaux q n1 n2) in (*Sers à recreer*)
	let auxauxaux a = match a with (etat b) -> let n = string_length b in let tmp = ref "" and n1 = ref 0 and n2 = ref 0 in let don = ref false in for i=0 to n-1 do if (b.[i] <> `/`) then begin tmp := !tmp ^ (string_of_char b.[i]); don := true end else (if (!don) then n2 := !n2 + 1 else n1 := !n1 + 1) done; ((etat !tmp), !n1, !n2) in (*Sert à decreer et à recup le compteur*)
	let rec auxauxauxL l = match l with [] -> [] |h::q -> let f (a,b,c) = a in (f (auxauxaux h)) :: (auxauxauxL q) in
	let A = union (lettreList_of_alphabet auto1.A) (lettreList_of_alphabet auto2.A) in (*On compile les deux alphabets*)
	let Q = union (aux1 auto1.Q) (aux2 auto2.Q) in (*On compile tous les états possibles : on double les états car on les mets bout à bout finalement*)
	let I = (aux1 auto1.I) in (*On part du premier*)
	let F = (aux2 auto2.F) in (*On finit par le deuxième*)
	(*Puis si on arrive sur un auto1.F il faut qu'on soit redirigé en plus vers tout les auto2.I*)
	(*On decreait l'état duquel on vient, et on reconstruit l'arrivé en conséquence*)
	(*Ca c'est si on change pas d'automate, sinon il faut recreer en fonction de l'arrivé : c'est pour auto2.I*)
	let d q a = match q with |qq -> let rec aux l ll = match l with [] -> false |h::q -> (mem h ll) || (aux q ll) in let q, n1, n2 = auxauxaux qq in if (*aux (auto1.d qq a) auto1.F*) (*A changer*) q = (etat "debut") then union (union (auxaux (auto1.d qq a) n1 n2) (aux2 (auxaux (auto2.I) (n1-1) (n2-1)))) (auxaux (auto2.d q a) n1 n2) else union (auxaux (auto1.d q a) n1 n2) (auxaux (auto2.d q a) n1 n2) in
	let dd q a = (d q a) in (*On vire tous les trucs inutiles -> à la fin :)*)
	{A = (alphabet A); Q = Q; I = I; F = F; d = dd};;

let creationUnion auto1 auto2 =
	let rec aux l = match l with [] -> [] |(etat a, etat b)::q -> (etat (a ^ "_" ^ b)) :: (aux q) in
	let A = union (lettreList_of_alphabet auto1.A) (lettreList_of_alphabet auto2.A) in (*On compile les deux alphabets*)
	let Q = aux (produit auto1.Q auto2.Q) in (*Il faut creer des états couple*)
	let I = aux (produit auto1.I auto2.I) in
	let F = aux (union (produit auto1.F auto2.Q) (produit auto1.Q auto2.F)) in
	let d q a = match q with (etat str) -> 
		let n = string_length str in
		let debut = ref false in
		let tmp1 = ref "" and tmp2 = ref "" in
		for i=0 to n-1 do
			if !debut = false && str.[i] = `_` then debut := true else begin
			if !debut then tmp2 := !tmp2 ^ (string_of_char str.[i]) else tmp1 := !tmp1 ^ (string_of_char str.[i]); end
		done;
		aux (produit (auto1.d (etat !tmp1) a) (auto2.d (etat !tmp2) a)) in
	{A = (alphabet A); Q = Q; I = I; F = F; d = d};;

let creationIntersection auto1 auto2 =
	let rec aux l = match l with [] -> [] |(etat a, etat b)::q -> (etat (a ^ "_" ^ b)) :: (aux q) in
	let A = union (lettreList_of_alphabet auto1.A) (lettreList_of_alphabet auto2.A) in (*On compile les deux alphabets*)
	let Q = aux (produit auto1.Q auto2.Q) in (*Il faut creer des états couple*)
	let I = aux (produit auto1.I auto2.I) in
	let F = aux (produit auto1.F auto2.F) in
	let d q a = match q with (etat str) -> 
		let n = string_length str in
		let debut = ref false in
		let tmp1 = ref "" and tmp2 = ref "" in
		for i=0 to n-1 do
			if str.[i] = `_` then debut := true else begin
			if !debut then tmp2 := !tmp2 ^ (string_of_char str.[i]) else tmp1 := !tmp1 ^ (string_of_char str.[i]); end
		done;
		aux (produit (auto1.d (etat !tmp1) a) (auto2.d (etat !tmp2) a)) in
	{A = (alphabet A); Q = Q; I = I; F = F; d = d};;

let creationEtoilage auto =
	let A = auto.A in
	let Q = auto.Q in
	let I = auto.I in
	let F = auto.F in (*On interdit le mot vide*)
	let d q a = match q with |q -> let rec aux l ll= match l with [] -> false |h::q -> (mem h ll) || (aux q ll) in if (aux (auto.d q a) auto.F) then union (auto.d q a) auto.I else (auto.d q a) in
	{A = A; Q = Q; I = I; F = F; d = d};;

let creationSeul (lettre str) = 
	let A = [(lettre str)] in
	let Q = [(etat "debut"); (etat str)] in
	let I = [(etat "debut")] in
	let F = [(etat str)] in
	let d q a = match q with |(etat "debut") when a = (lettre str) -> [(etat str)] |_ -> [] in
	{A = (alphabet A); Q = Q; I = I; F = F; d = d};;

let rec creationAutomateAux lang = match lang with
	|(Concaténation (a, b)) -> creationConcatenation (creationAutomateAux a) (creationAutomateAux b)
	|(Union (a, b)) -> creationUnion (creationAutomateAux a) (creationAutomateAux b)
	|(Etoilage a) -> creationEtoilage (creationAutomateAux a)
	|(Seul a) -> let rec aux l = match l with [] -> {A=(alphabet []); Q=[]; I=[]; F=[]; d=(let d q a = [] in d)} |[a] -> creationSeul a (*Oui ce cas est utile*) |h::q -> creationConcatenation (creationSeul h) (aux q) in aux (lettreList_of_mot a);;

(*On l'émonde maitenant car c'est mieux pour l'affichage*)
(*On garde que les états coaxiaux/utiles*)
let creationAutomate lang =
	let AA = creationAutomateAux lang in
	let utile q = let n = list_length AA.Q and espoir = ref false and tmp = ref [q] in
	for i=0 to n-1 do tmp := union !tmp (compilation (image2 AA.d !tmp (lettreList_of_alphabet AA.A))); espoir := !espoir || ((intersect !tmp AA.F) <> []); done; !espoir in
	let rec epur l = match l with [] -> [] |h::q when utile h -> h :: (epur q) |_::q -> epur q in
	let QQ = epur AA.Q in
	let dd q a = (intersect QQ (AA.d q a)) in (*patch la fonction epur et l'utiliser*)
	{A=AA.A; Q=QQ; I=AA.I; F=AA.F; d=dd};;

let creationAutomateRapide lang =
	let AA = creationAutomateAux lang in
	let dd q a = (intersect AA.Q (AA.d q a)) in
	{A=AA.A; Q=AA.Q; I=AA.I; F=AA.F; d=dd};;
(*Un exemple de language : le language a*b**)

let L = creation "abacac";;
(*let L = Union (Seul (mot [lettre "a"]), Seul (mot [lettre "b"]));;*)
let auto = creationAutomateRapide L;;
clear 2;;
affiche (auto);;
auto.d (etat "debut_debut") b;;


(*On gère les codes : on suppose les lettres forment un code (ie que ya pas de troll)*)
(*On doit verifier si une liste de mots forme un code ; les mots sont des lettres list, et les lettres des strings : deux trucs sont pareil si les strs sont pareil : cf la remarque plus haut*)
(*Lettre dispo par ex : a b c d*)
let creationMot str = let n = string_length str in
	let res = make_vect n (lettre "") in
	for i=0 to n-1 do
		res.(i) <- (lettre (string_of_char str.[i]))
	done;
	(mot (list_of_vect res));;
let rec creationCandidat l = match l with
	|[] -> []
	|h::q -> (creationMot h) :: (creationCandidat q);;
let rec egaliterMot (mot m1) (mot m2) = match m1, m2 with
	|[], [] -> true
	|[], _ -> false
	|_, [] -> false
	|(lettre h)::q, (lettre hh)::qq -> (h=hh) && (egaliterMot (mot q) (mot qq));;
let rec egaliterMotTmp (mot m1) (mot m2) = match m1, m2 with
	|[], [] -> true
	|[], _ -> true
	|_, [] -> true
	|(lettre h)::q, (lettre hh)::qq -> (h=hh) && (egaliterMotTmp (mot q) (mot qq));; 
let prefix =! a b = egaliterMot a b;;
let prefix ==! a b = egaliterMotTmp a b;;
(*Pour verifier si un language est un code :
	+On part d'un mot disponible
	+On essaye de le refaire avec un autre mot ->
		+Une fois qu'on a ces deux mots en compétition on regarde le moins long et on lui rajoute les trucs dispos
		+Et recursivement ainsi de suite
	+Soit on trouve une deux trucs identiques auquel cas c'est finit
	+Soit on trouve rien et on recommence sur tout les autres mots de départ
	+Une fois qu'on les a tous testé on saitque ça marchera pas : on affiche un exemple par mot*)

(*On code déjà quand ya deux mots en compétition et le language de dispo : fonction recursives*)
let rec lenm (mot m) = match m with
	[] -> 0
	|h::q -> 1 + (lenm (mot q));;
let ajout (mot m) (mot l) = mot (m @ l);;
let prefix +! a b = ajout a b;;
let rec affichage lm = match lm with [] -> "" |(mot l)::q -> let rec aux l = match l with [] -> "" |(lettre h)::q -> h ^ (aux q) in (aux l) ^ "/" ^ (affichage q);;
(*C'est des couples : le premier est le mot en entier et le deuxieme est la liste des mots pour le constituer*)
let rec tentativeMatchAux m1 m2 dispo = let n1 = lenm (fst m1) and n2 = lenm (fst m2) in
	print_endline "";
	print_string ("Debut : " ^ ((affichage (snd m1)) ^ " -- " ^ ((affichage (snd m2)))));
	if (n1 = n2) then if (fst m1) = (fst m2) then begin print_string ("\n\nGg wp voici la combinaison : " ^ (affichage (snd m1)) ^ " >< " ^ (affichage (snd m2))); true end else false else begin
	if (n1 < n2) then begin
		let n = vect_length dispo in
		let ok = ref [] in
		for i=0 to n-1 do
			print_string (" Itér : " ^ ((affichage ((snd m1) @ [dispo.(i)])) ^ " -- " ^ ((affichage (snd m2)))));
			if (not (dispo.(i) =! (fst m2))) then
			let tmp = ((fst m1) +! dispo.(i), (snd m1) @ [dispo.(i)]) in
			if (fst tmp) ==! (fst m2) then (*Compatible*) ok := tmp :: !ok
		done;
		if (ok = ref []) then false else
		(*On continue avec l'autre fonction qui gère des listes*)
		tentativeMatch !ok m2 dispo
	end
	else 
		tentativeMatchAux m2 m1 dispo (*On inverse les rôles*)
	end
and
tentativeMatch lm m dispo = match lm with
	|[] -> false
	|h::q when (tentativeMatchAux h m dispo) = true -> true
	|h::q -> (tentativeMatch q m dispo);;
let rec remove l e = match l with [] -> [] |h::q when h=!e -> q |h::q -> h :: (remove q e);;
let rec checkCodeAux l acc = match l with
	|[] -> print_endline "\n\nC'est un code lul \o/"; true
	|h::q when (tentativeMatchAux (h, [h]) ((mot []), []) (vect_of_list acc)) = true -> false
	|h::q -> (checkCodeAux q acc);;
let checkCode l = checkCodeAux l l;;

let l1 = creationCandidat ["aba"; "ba"; "aa"];;
checkCode l1;;
let l1 = creationCandidat ["abab"; "ba"; "aba"];;
checkCode l1;;


(*On fait les residuels : pour voir le nombre minimum d'etats : comme d'hab on bruteforce*)
(*On cherche d'abord le residuel pour un mot : le u-1L = {les mots qui commencent par u} : trivialement si u donne vide alors uv donne tj vide*)
(*On pourra faire recursivement avec (uv)-1L = v-1(u-1(L)) --> suffit de prog pour une seule lettre*)
(*Faudra aussi comparer deux languages voir si ils sont egaux : bruteforce ? car on peut pas faire des tests structurels*)
(*Rappel : on a type language = Concaténation of language*language | Union of language*language | Etoilage of language | Seul of mot*)
let rec verifResiduLettre lang letre = match lang with
	|(Concaténation (a, b)) -> verifResiduLettre a letre
	|(Union (a, b)) ->  verifResiduLettre a letre || verifResiduLettre b letre
	|(Etoilage a) -> verifResiduLettre a letre
	|(Seul (mot a)) -> let aux b c = match (b, c) with (lettre b), (lettre c) -> b=c in if a=[] then false else aux (hd a) letre;;

let rec residuLettre lang letre = if (verifResiduLettre lang letre) then match lang with
	|(Concaténation (a, b)) -> ConcaténationBis (residuLettre a letre, b)
	|(Union (a, b)) when verifResiduLettre a letre && verifResiduLettre b letre ->  (Union (residuLettre a letre, residuLettre b letre))
	|(Union (a, b)) when verifResiduLettre a letre -> residuLettre a letre
	|(Union (a, b)) when verifResiduLettre b letre -> residuLettre b letre
	|(Etoilage a) -> (ConcaténationBis (residuLettre a letre, Etoilage a))
	|(Seul (mot a)) when a = [] -> Seul mot_vide
	|(Seul (mot a)) -> let aux b c = match (b, c) with (lettre b), (lettre c) when b=c -> true |_-> false in 
		if a=[] then Seul mot_vide else if aux (hd a) letre then Seul (mot (tl a)) else Seul mot_vide
	|_ -> failwith "residuLettre -> erreur de match qui n'est pas sensé arrivé : go patch l'union"
	else Seul mot_vide;;

let rec residuMot lang motTmp = match rev (lettreList_of_mot motTmp) with
	|[] -> lang
	|h::q -> residuMot (residuLettre lang h) (mot (rev q));;

L;;
ecrit L;;
let LL = residuLettre L a;;
ecrit LL;;
residuLettre LL b;;
residuMot L (mot (rev [lettre "a"; lettre "b"; lettre "a"; lettre "c"]));;

(*On nous donne l'alphabet des 2 languages (ou une union de leur alphabet c'est idem) : une liste des lettres toutes distinctes*)
(*Pour regarder si deux languages sont égaux on bruteforce tous les mots d'une longueur donnée*)
let rec appartient lang motTmp prec = match lang with
	|(Concaténation (a, b)) -> 
		let tmp = vect_of_list (lettreList_of_mot motTmp) in
		let n = vect_length tmp in
		let res = ref false in
		for i=0 to n-1 do
			let tmp1 = sub_vect tmp 0 i and tmp2 = sub_vect tmp i (n-i) in
			res := !res || ((appartient a (mot (list_of_vect tmp1)) prec) && (appartient b (mot (list_of_vect tmp2)) prec))
		done;
		!res
	|(Union (a, b)) ->  appartient a motTmp prec || appartient b motTmp prec
	|(Etoilage a) ->
		if (list_length (lettreList_of_mot motTmp)) = 0 then true else begin
		let tmp = ref a in
		let res = ref false in
		for i=0 to prec-1 do
			res := !res || (appartient !tmp motTmp prec);
			tmp := Concaténation (a, !tmp)
		done;
		!res;
		end
	|(Seul (mot a)) -> a = lettreList_of_mot motTmp;;

let rec egaliterAux lang1 lang2 alphabetTmp prec acc res precBis = match prec with 0 -> !res |prec ->
	let alVect = vect_of_list (lettreList_of_alphabet alphabetTmp) in
	let n = vect_length alVect in
	for i=0 to n-1 do
		res := !res && (egaliterAux lang1 lang2 alphabetTmp (prec-1) (alVect.(i)::acc) res precBis) && ((appartient lang1 (mot acc) precBis) = (appartient lang2 (mot acc) precBis))
	done;
	!res;;

let egaliterLangage lang1 lang2 alphabetTmp prec = egaliterAux lang1 lang2 alphabetTmp prec [] (ref true) prec;; (*Faudrati reflechir sur ce precBis*)

(*On peut enfin lister/denombrer tous les résidus d'un language + alphabet*)
(*On bourrine tout jusqu'à prec pour filtrer ceux qui sont égaux et voila*)

(*On le fait en impératif : liste de tous les mots into listes des residuels par parcours des mots*)
let listeMot alphabetTmp prec = let rec aux al prof ori acc = match prof with 0 -> [mot acc] |prof -> match al with
	|[] -> aux ori (prof-1) ori acc
	|h::q -> ((aux ori (prof-1) ori (h::acc)) @ (aux q prof ori acc)) in aux (lettreList_of_alphabet alphabetTmp) prec (lettreList_of_alphabet alphabetTmp) [];;

let listeResiduels lang alph prec =
	let rec aux l lang alph prec = match l with [] -> true |h::q -> (not (egaliterLangage h lang alph prec)) && (aux q lang alph prec) in
	let aTest = vect_of_list (listeMot alph prec) in
	let n = vect_length aTest in
	let res = ref [] in
	for i=0 to n-1 do
		let tmp = residuMot lang aTest.(i) in
		if not (tmp = Seul mot_vide) then
		if (aux !res tmp alph prec) then res := tmp :: !res
	done;
	!res;;

let rec ecritListeResiduels l = match l with [] -> "" |[h] -> (ecrit h) |h::q -> (ecrit h) ^ " -- " ^ (ecritListeResiduels q);;

ecrit L;;
ecritListeResiduels  (listeResiduels L ABC 6);;
