%%% Autori:
%%% Caputo Lorenzo 894528
%%% Groppo Gabriele 902238

%%% _*_ Mode: Prolog _*_

%%% oop.pl

%%% Predicati dinamici
:- dynamic class/1.
:- dynamic inst/1.

%%% Definisce una classe: 1 - ho <class-name> e <parents> come parametri
def_class(ClassName, Parents) :-
    atom(ClassName),
    not(is_class(ClassName)),
    is_parents_list(Parents),
    assertz(class([ClassName, Parents, _])), !.

%%% Definisce una classe: 2 - ho <class-name>, <parents> e <parts> come
%%% parametri
%%% caso in cui <parts> contiene la definizione di un metodo
def_class(ClassName, Parents, Parts) :-
    atom(ClassName),
    not(is_class(ClassName)),
    is_parents_list(Parents),
    is_list(Parts),
    %%% Se <parts> contiene elementi diversi da field() o method(), fallisce
    fields_structure(Parts, _),
    is_method_present(Parts), !,
    setof(Method, methods_structure(Parts, Method), Methods),
    create_methods(Methods, ClassName),
    assertz(class([ClassName, Parents, Parts])), !.

%%% caso in cui <parts> NON contiene la definizione di un metodo
def_class(ClassName, Parents, Parts) :-
    atom(ClassName),
    not(is_class(ClassName)),
    is_list(Parts),
    is_parents_list(Parents),
    %%% Se <parts> contiene elementi diversi da field() o method(), fallisce
    fields_structure(Parts, _),
    assertz(class([ClassName, Parents, Parts])), !.

%%% Controllo che Parents sia una lista di classi senza classi duplicate
is_parents_list(Parents) :-
    is_list(Parents),
    maplist(is_class, Parents),
    not(contains_duplicates(Parents)), !.

%%% chiamo method_definition per ogni metodo presente nella lista
create_methods([], _).

create_methods([Method | Rest], ClassName) :-
    method_definition(Method, ClassName),
    create_methods(Rest, ClassName), !.

%%% costruisco il metodo e lo carico nella base della conoscenza
method_definition(method(MethodName, Args, MethodBody), ClassName) :-
    append([this], Args, MethodArgs),
    append([MethodName], MethodArgs, Head),
    Term =.. Head,
    term_to_atom(MethodName, Name),
    term_to_atom(Term, MethodHead),
    term_to_atom(MethodBody, BodyNoCheck),
    term_to_atom(ClassName, Class),
    atom_concat('field(this, ', Name, Step1),
    atom_concat(Step1, ', MC1),', Step2),
    atom_concat(Step2, 'field(', Step3),
    atom_concat(Step3, Class, Step4),
    atom_concat(Step4, ', ', Step5),
    atom_concat(Step5, Name, Step6),
    atom_concat(Step6, ', MC2),', Step7),
    atom_concat(Step7, 'MC1 = MC2', Step8),
    atom_concat(Step8, ',', Step9),
    atom_concat(Step9, BodyNoCheck, Step10),
    atom_concat(MethodHead, ' :- ', Step11),
    atom_concat(Step11, Step10, Step12),
    atom_concat(Step12, ', !.', Step13),
    atom_string(Step13, Step14),
    convert_this(Step14, MethodAtom),
    term_to_atom(Method, MethodAtom),
    assertz(Method).

%%% converto la struttura del metodo, passata come stringa, in una lista di char
convert_this(MethodNoThisString, MethodAtom) :-
    atom_chars(MethodNoThisString, CharList),
    replace_this(CharList, NewCharList),
    atom_chars(MethodAtom, NewCharList), !.

%%% sostiuisco "this" con "This", avendo così la variabile logica
replace_this([], []).

replace_this(['t', 'h', 'i', 's' | Rest], ['T', 'h', 'i', 's' | NewRest]) :-
    replace_this(Rest, NewRest).

replace_this([X | Rest], [X | NewRest]) :-
    replace_this(Rest, NewRest).

%%% Estraggo tutti i campi da Part e controllo la sintassi
%%% field(Name,Value) oppure field(Name, Value, Type)
%%% Controllo la correttezza tipo-valore, o che vi sia un metodo
fields_structure([], []).

fields_structure([Part | Rest], [Part | Tail]) :-
    Part = field(_Name, _Value),
    fields_structure(Rest, Tail).

fields_structure([Part | Rest], [Part | Tail]) :-
    Part = field(_Name, Value, Type),
    valid_field_type(Value, Type), !,
    fields_structure(Rest, Tail).

%%% Ho estratto un metodo
fields_structure([method(_Name, _Args, _Body) | Rest],  Tail) :-
    fields_structure(Rest, Tail).

%%% Controlla la corretta corrispondenza tra valore e tipo
valid_field_type(Value, Type) :-
    Function =.. [Type, Value],
    call(Function), !.

%%% InstanceName è un simbolo: aggiungo alla base della conoscenza
%%% l'istanza creata, se non è già presente nella base della conoscenza.
make(InstanceName, ClassName, Parameters) :-
    atom(InstanceName),
    not(is_instance(InstanceName)),
    atom(ClassName),
    is_class(ClassName),
    is_list(Parameters),
    type_checking(Parameters, ClassName),
    assertz(inst([InstanceName, ClassName, Parameters])), !.

%%% InstanceName è un simbolo: se InstanceName è già presente nella base della 
%%% conoscenza, viene rimpiazzata con la nuova versione di se stessa
make(InstanceName, ClassName, Parameters) :-
    atom(InstanceName),
    is_instance(InstanceName),
    atom(ClassName),
    is_class(ClassName),
    is_list(Parameters),
    type_checking(Parameters, ClassName),
    retract(inst([InstanceName, _, _])),
    assertz(inst([InstanceName, ClassName, Parameters])), !.

%%% InstanceName è una variabile: unifico la variabile con l'istanza appena
%%% creata
make(InstanceName, ClassName, Parameters) :-
    var(InstanceName),
    atom(ClassName),
    is_class(ClassName),
    is_list(Parameters),
    type_checking(Parameters, ClassName),
    inst([InstanceName, ClassName, Parameters]), !.

%%% InstanceName è un termine: unifico il termine con l'istanza appena creata
make(InstanceName, ClassName, Parameters) :-
    atom(ClassName),
    is_class(ClassName),
    is_list(Parameters),
    type_checking(Parameters, ClassName),
    InstanceName =.. Instance,
    Instance = [_, S | _],
    is_instance(S), !.

%%% Utilizzata come correttore di errori, richiama make senza passare
%%% alcun parametro
make(InstanceName, ClassName) :-
    make(InstanceName, ClassName, []), !.

%%% controllo di corrispondenza di tipo tra ogni campo nella classe e le sue
%%% superclassi
type_checking([], _).

type_checking([Name = _Value | Rest], ClassName) :-
    get_parents_field_value([ClassName], Name, _, Type),
    Type == nil,
    type_checking(Rest, ClassName), !.

type_checking([Name = Value | Rest], ClassName) :-
    get_parents_field_value([ClassName], Name, _, Type),
    Type \== nil,
    Funct =.. [Type, Value],
    call(Funct), !,
    type_checking(Rest, ClassName), !.

%%% controllo che <class-name> sia il nome di una classe
is_class(ClassName) :-
    current_predicate(class/1), !,
    class([ClassName, _, _]).

%%% controllo che <value> sia il nome di una istanza qualsiasi
%%% <value> viene passata così per come è
is_instance(Value) :-
    current_predicate(inst/1),
    inst([Value | _]), !.

%%% controllo che <value> sia il nome di una istanza qualsiasi
%%% <value> viene passata scomposta nelle sue parti:
%%% ([InstanceName, ClassName, Parameters])
is_instance(Value) :-
    current_predicate(inst/1),
    inst(Value), !.

%%% Controllo se <value> sia il nome di una istanza che ha <class-name> come
%%% superclasse
is_instance(Value, ClassName) :-
    atom(ClassName),
    Value = [InstanceName | _],
    inst([InstanceName, Class |  _]),
    get_parents_list(Class, Parents),
    member(ClassName, Parents).

%%% recupero istanza con nome <instance-name> e la unifico con <instance>
inst(InstanceName, [InstanceName | Instance]) :-
    atom(InstanceName),
    current_predicate(inst/1), !,
    inst([InstanceName | Instance]), !.

%%% estraggo valore di <field-name> direttamente dall'istanza stessa
field(Instance, FieldName, Result) :-
    is_instance(Instance),
    atom(FieldName),
    get_field_value(Instance, FieldName, Result, _), !.

%%% eredito i campi dalle superclassi: Instance è il nome di una istanza
field(Instance, FieldName, Result) :-
    is_instance(Instance),
    atom(FieldName),
    inst([Instance, ClassName | _]),
    get_parents_field_value([ClassName], FieldName, Result, _Type), !.

%%% eredito i campi dalle superclassi: Instance è il nome di una classe
field(Instance, FieldName, Result) :-
    is_class(Instance),
    atom(FieldName),
    class([Instance, _, _]),
    get_parents_field_value([Instance], FieldName, Result, _Type), !.

%%% Field riceve istanza per intero e preleva il InstanceName
field([InstanceName | _], FieldName, Result) :-
    field(InstanceName, FieldName, Result), !.

%%% estraggo il valore di un campo dall'istanza <instance>
fieldx(Instance, [Field], Result) :-
    atom(Field),
    field(Instance, Field, Result), !.

%%% estraggo il valore di più campi dall'istanza <instance>
fieldx(Instance, [Head | Rest], Result) :-
    atom(Head),
    field(Instance, Head, NewInstance),
    is_instance(NewInstance),
    fieldx(NewInstance, Rest, Result), !.

%%% Caso Base
get_parents_field_value([ClassName | _], FieldName, Result, Type) :-
    class([ClassName, _, _]),
    get_field_value(ClassName, FieldName, Result, Type).

%%% Estraggo ricorsivamente i parents dall'albero delle superclassi,
%%% ne creo una lista e ritorno il valore del campo
get_parents_field_value([ClassName | Parents], ParentsList, Result, Type) :-
    class([ClassName, ClassParents, _]),
    append(ClassParents, Parents, NewList),
    get_parents_field_value(NewList, ParentsList, Result, Type).

%%% ricevo il nome dell'istanza: ricavo istanza stessa con inst/2 e
%%% richiamo get_field_value/3 passandogli l'istanza stessa
get_field_value(InstanceName, FieldName, Value, Type) :-
    inst(InstanceName, Instance),
    get_field_value(Instance, FieldName, Value, Type).

get_field_value(Instance, FieldName, Result, Type) :-
    get_class(Instance, Class),
    get_field_value(Class, FieldName, Result, Type), !.

%%% Caso Base (istanza): <field-name> è in testa alla lista dei parametri
get_field_value([_, _, [FieldName = Value | _]], FieldName, Value, nil).

get_field_value([_, _, [field(FieldName, Value) | _]], FieldName, Value, nil).

get_field_value([_, _, [field(FieldName, Value, Type) | _]], 
FieldName, Value, Type).

%%% Caso Ricorsivo (istanza): scorro la lista dei parametri
get_field_value([_, _, [_ | Rest]], FieldName, Value, Type) :-
    get_field_value([_, _, Rest], FieldName, Value, Type).


get_class(ClassName, [ClassName | Rest]) :-
    current_predicate(class/1),
    class([ClassName | Rest]).

%%% Raccolgo la lista delle superclassi della classe Class
get_parents_list(Class, Parents) :-
    setof(Parent, get_parents([Class], Parent), Parents).

%%% Caso Base
get_parents([ClassName | _], ClassName) :-
    class([ClassName, _, _]).

%%% Estraggo ricorsivamente i parents nella struttura gerarchica delle
%%% classi e ne creo una lista
get_parents([ClassName | Parents], ParentsList) :-
    class([ClassName, ClassParents, _]),
    append(ClassParents, Parents, NewList),
    get_parents(NewList, ParentsList).

%%% Controlla se la lista contiene la definizione di almeno un metodo
is_method_present([Head | _]) :-
    Head = method(_Name, _Args, _Body), !.

is_method_present([_ | Tail]) :-
    is_method_present(Tail).

is_method_present([]) :- fail.

%%% Controllo la sintassi di ogni metodo della lista dei metodi
%%% method(Name, Args, Body)
methods_structure([Method | _], Method) :-
    Method = method(_Name, Args, _Body),
    is_list(Args).

methods_structure([_ | Rest],  Method) :-
    methods_structure(Rest, Method).

%%% Controlla che una lista non contenga duplicati
contains_duplicates([]) :- false.

contains_duplicates([Head | Tail]) :-
    member(Head, Tail), !.

contains_duplicates([_ | Tail]) :-
    contains_duplicates(Tail), !.

%%% End of File -- oop.pl
