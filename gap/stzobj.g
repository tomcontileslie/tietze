
################################################################################
# The Stz Object (name pending)
# Idea is to have a single object containing generators and relations that can
# have the relations be presented in a number of different computation-friendly
# or user-friendly formats (LetterRepAssocWord, ExtRepOfObj, user-readable
# strings). Ideally never seen by the user, but used internally to - among other
# things - reduce the relations of an FP semigroup/monoid to a simple form
#
# I argue: no need for IsMutable/IsImmutable/etc, since StzPresentation likely
# is never seen by the user, so as long as it is contained to the stz reduction
# (as it likely will be) there will be no issues.
################################################################################

# DeclareOperation("StzPresentation", [IsList, IsList]);
DeclareOperation("StzPresentation", [IsFpSemigroup]);
DeclareCategory("IsStzPresentation", IsList);
#DeclareRepresentation("IsStzPresentationRep", IsStzPresentation and IsPositionalObjectRep,
#                        3);


# Can add extra representations as attributes?
# Maybe use 'representation' instead
DeclareAttribute("RelationsOfStzPresentation", IsStzPresentation);
DeclareOperation("LetterRepRelationsOfStzPresentation", [IsStzPresentation]);
DeclareOperation("SetRelationsOfStzPresentation", [IsStzPresentation, IsList]);
DeclareAttribute("GeneratorsOfStzPresentation", IsStzPresentation);
DeclareOperation("SemigroupOfStzPresentation", [IsStzPresentation]);
DeclareAttribute("UnreducedSemigroupOfStzPresentation", IsStzPresentation);

DeclareAttribute("UnreducedFpSemigroupOfFpSemigroup", IsFpSemigroup);

## Perhaps deprecated: will be passing a semigroup itself to the reduction
## function anyway so who cares about doing this constructor
##
# InstallMethod(StzPresentation,
# "for a list of generators, and a list of relations by external representation",
# [IsList, IsList],
# function(gens, rels)
#     local out, type;

#     # This is definitely the wrong way to do this
#     # Not sure what "StzFamily" does but seems to work
#     type := NewType(NewFamily("StzFamily", IsStzPresentation),
#                     IsStzPresentation and IsAttributeStoringRep);

#     # Actual underlying data
#     out := rec(gens := gens, rels := rels);

#     # Example
#     return ObjectifyWithAttributes(out, type,
#                                     RelationsOfStzPresentation, out!.rels,
#                                     GeneratorsOfStzPresentation, out!.gens);
# end);

InstallMethod(StzPresentation, "for a finitely presented semigroup",
[IsFpSemigroup],
function(S)
    local out, rels, type;

    type := NewType(NewFamily("StzFamily", IsStzPresentation),
                    IsStzPresentation and IsAttributeStoringRep);

    rels := List(RelationsOfFpSemigroup(S),
                 x -> [SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x[1])),
                       SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x[2]))]);

    out := rec(gens := List(GeneratorsOfSemigroup(S), x -> ViewString(x)), rels := rels, unreducedSemigroup := S);

    return ObjectifyWithAttributes(out, type,
                                    RelationsOfStzPresentation,
                                    out!.rels,
                                    GeneratorsOfStzPresentation,
                                    out!.gens,
                                    UnreducedSemigroupOfStzPresentation,
                                    out!.unreducedSemigroup);
end);

# Add checks cause this can break everything
InstallMethod(SetRelationsOfStzPresentation,
[IsStzPresentation, IsList],
function(stz, arg)
    if not ForAll(arg, IsList) or
        not ForAll(arg, x -> ForAll(x, IsList)) or
        not ForAll(arg, x -> ForAll(x, y -> ForAll(y,IsPosInt))) then
        ErrorNoReturn("parameter <arg> must be a list of relations of the ",
                    " form letter then exponent,");
    fi;
    stz!.rels := arg;
end);

InstallMethod(RelationsOfStzPresentation,
[IsStzPresentation],
function(stz)
    return stz!.rels;
end);

InstallMethod(UnreducedSemigroupOfStzPresentation,
[IsStzPresentation],
function(stz)
    return stz!.unreducedSemigroup;
end);

# Storing as attribute kinda breaks it since
InstallMethod(LetterRepRelationsOfStzPresentation,
[IsStzPresentation],
function(stz)
    local out, rels, rel, relSide, i, exp, letter, newRels, newRelSide, newRel,w;
    rels := RelationsOfStzPresentation(stz);
    out := [];

    # There's something here, I'm fairly sure
    # w := ObjByExtRep(FamilyObj(stz!.gens[1]), stz!.rels);

    for rel in [1..Length(rels)] do
        newRel :=[];
        for relSide in [1,2] do
            newRelSide := [];
            for i in [1 .. Length(rels[rel][relSide])/2]*2 do
                letter:=rels[rel][relSide][i-1];
                exp:=rels[rel][relSide][i];
                newRelSide:=Concatenation(newRelSide,List([1..exp], x-> letter));
            od;
            Append(newRel, [newRelSide]);
        od;
        Append(out, [newRel]);
    od;

    return out;
end);

InstallMethod(SemigroupOfStzPresentation,
[IsStzPresentation],
function(stz)
    local out, F, rels, gens;
    F := FreeSemigroup(stz!.gens);
    rels := stz!.rels;
    gens := GeneratorsOfSemigroup(F);
    # TCL: TODO: I think AssocWordByLetterRep is better for next line
    out := F / List(rels, x -> List(x, y -> Product(List(y, z -> gens[z]))));
    SetUnreducedFpSemigroupOfFpSemigroup(out,
                                    UnreducedSemigroupOfStzPresentation(stz));
    return out;
end);

# DeclareAttribute("ReducedFpSemigroupOfFpSemigroup", IsFpSemigroup);???? maybe
