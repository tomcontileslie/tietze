
# Searches through the relations of stzObj and replaces each instance of subword
# with newWord, except if the entire relation is exactly subWord (preserving a
# newly created relation)
# newWord should be stricly less than subword or else may be an infinite
# sequence (maybe just handle this?)
StzReplaceSubword := function(stz, subword, newWord)
    local out, gens, rels, newRels, rel1, rel2, i;
    # Using format of LetterRepAssocWord, can change
    # Global variable eg STZ_GENS := 1, STZ_RELS := 2?
    rels := RelationsOfStzPresentation(stz);

    newRels := List([1 .. Length(rels)], x -> []);
    for i in [1 .. Length(rels)] do    
        #if rels[i][1] = subword then
        #    rel1 := rels[i][1];
        #else
            rel1 := StzReplaceSubwordRel(rels[i][1], subword, newWord);
        #fi;
        #if rels[i][2] = subword then
        #    rel2 := rels[i][2];
        #else
            rel2 := StzReplaceSubwordRel(rels[i][2], subword, newWord);
        #fi;
        newRels[i] := [rel1, rel2];
    od;
    return newRels;
end;

# Searches a single LetterRepAssocWord list and replace instances of subword
# with newWord
StzReplaceSubwordRel := function(letterRep, subword, newWord)
    local out, pos;
    out := [];
    pos := PositionSublist(letterRep, subword);
    if pos <> fail then
        for i in [1 .. pos - 1] do
            Append(out, [letterRep[i]]);
        od;
        for i in [1 .. Length(newWord)] do
            Append(out, [newWord[i]]);
        od;
        for i in [pos + Length(subword) .. Length(letterRep)] do
            Append(out, [letterRep[i]]);
        od;
        pos := PositionSublist(out, subword);
        if pos <> fail then
            return StzReplaceSubwordRel(out, subword, newWord);
        else
            return out;
        fi;
    else
        return letterRep;
    fi;
end;

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

# Current relations in the process of being reduced
DeclareAttribute("RelationsOfStzPresentation", IsStzPresentation);

# Letter representation of the current relations
DeclareOperation("LetterRepRelationsOfStzPresentation", [IsStzPresentation]);

# Setter for relations, checks that list is in ext rep form
DeclareOperation("SetRelationsOfStzPresentation", [IsStzPresentation, IsList]);

DeclareAttribute("GeneratorsOfStzPresentation", IsStzPresentation);

DeclareOperation("SetGeneratorsOfStzPresentation", [IsStzPresentation, IsList]);

# Constructs new fp semigroup out of current relations and generators
DeclareOperation("SemigroupOfStzPresentation", [IsStzPresentation]);

# Stores original semigroup before reductions
DeclareAttribute("UnreducedSemigroupOfStzPresentation", IsStzPresentation);

# Stores a map between the words of each semigroup (how?)
# Change as relations change
# Otherwise must keep track of all tietze transforms i suppose
DeclareAttribute("MapToUnreducedFpSemigroup", IsStzPresentation);

DeclareOperation("SetMapToUnreducedFpSemigroup", [IsStzPresentation, IsPosInt, IsList]);

DeclareOperation("MapToUnreducedFpSemigroupReplaceSubword", [IsStzPresentation, IsList, IsList]);

# FP semigroup attributes
DeclareAttribute("UnreducedFpSemigroupOfFpSemigroup", IsFpSemigroup);
DeclareAttribute("MapToUnreducedFpSemigroup", IsFpSemigroup);

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
                    IsStzPresentation and IsComponentObjectRep);

    rels := List(RelationsOfFpSemigroup(S),
                x -> [LetterRepAssocWord(x[1]), LetterRepAssocWord(x[2])]);

    out := rec(gens := List(GeneratorsOfSemigroup(S), x -> ViewString(x)),
                rels := rels,
                unreducedSemigroup := S,
                mapToUnreducedFpSemigroup := List([1..Length(GeneratorsOfSemigroup(S))], x -> [x]));

    return ObjectifyWithAttributes(out, type,
                                    RelationsOfStzPresentation,
                                    out!.rels,
                                    GeneratorsOfStzPresentation,
                                    out!.gens,
                                    UnreducedSemigroupOfStzPresentation,
                                    out!.unreducedSemigroup,
                                    MapToUnreducedFpSemigroup,
                                    out!.mapToUnreducedFpSemigroup);
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

InstallMethod(MapToUnreducedFpSemigroup,
[IsStzPresentation],
function(stz)
    return stz!.mapToUnreducedFpSemigroup;
end);

InstallMethod(GeneratorsOfStzPresentation,
[IsStzPresentation],
function(stz)
    return stz!.gens;
end);

InstallMethod(SetGeneratorsOfStzPresentation,
[IsStzPresentation, IsList],
function(stz, newGens)
    stz!.gens := newGens;
end);

# # Storing as attribute kinda breaks it since
# InstallMethod(LetterRepRelationsOfStzPresentation,
# [IsStzPresentation],
# function(stz)
#     local out, rels, rel, relSide, i, exp, letter, newRels, newRelSide, newRel,w;
#     rels := RelationsOfStzPresentation(stz);
#     out := [];

#     # There's something here, I'm fairly sure
#     # w := ObjByExtRep(FamilyObj(stz!.gens[1]), stz!.rels);

#     for rel in [1..Length(rels)] do
#         newRel :=[];
#         for relSide in [1,2] do
#             newRelSide := [];
#             for i in [1 .. Length(rels[rel][relSide])/2]*2 do
#                 letter:=rels[rel][relSide][i-1];
#                 exp:=rels[rel][relSide][i];
#                 newRelSide:=Concatenation(newRelSide,List([1..exp], x-> letter));
#             od;
#             Append(newRel, [newRelSide]);
#         od;
#         Append(out, [newRel]);
#     od;

#     return out;
# end);

InstallMethod(SemigroupOfStzPresentation,
[IsStzPresentation],
function(stz)
    local out, F, rels, gens;
    F := FreeSemigroup(stz!.gens);
    rels := RelationsOfStzPresentation(stz);
    gens := GeneratorsOfSemigroup(F);
    out := F / List(rels, x -> List(x, y -> Product(List(y, z -> gens[z]))));
    SetUnreducedFpSemigroupOfFpSemigroup(out,
                                    UnreducedSemigroupOfStzPresentation(stz));
    # May well break now but this MUST exist so its okay at the moment
    SetMapToUnreducedFpSemigroup(out,
                            MapToUnreducedFpSemigroup(stz));
    return out;
end);

InstallMethod(SetMapToUnreducedFpSemigroup,
[IsStzPresentation, IsPosInt, IsList],
function(stz, index, newMap)
    stz!.mapToUnreducedFpSemigroup[index] := newMap;
end);

DeclareOperation("SetMapToUnreducedFpSemigroup", [IsStzPresentation, IsList]);

InstallMethod(SetMapToUnreducedFpSemigroup,
[IsStzPresentation, IsList],
function(stz, newMaps)
    if not ForAll(newMaps, x -> IsList and ForAll(x, y -> IsPosInt)) then
        ErrorNoReturn("argument <newMaps> must be a list of positive integers,");
    fi;
    stz!.mapToUnreducedFpSemigroup := newMaps;
end);

InstallMethod(MapToUnreducedFpSemigroupReplaceSubword,
[IsStzPresentation, IsList, IsList],
function(stz, subWord, newSubWord)
    local newMaps;
    newMaps := List(stz!.mapToUnreducedFpSemigroup, x -> StzReplaceSubwordRel(x, subWord, newSubWord));
    stz!.mapToUnreducedFpSemigroup := newMaps;
end);

InstallMethod(Length,
[IsStzPresentation],
function(stz)
    local out, rels, rel;
    out := Length(stz!.gens);
    rels := RelationsOfStzPresentation(stz);
    for rel in rels do
        out := out + Length(rel[1]) + Length(rel[2]);
    od;
    return out;
end);

InstallMethod(ViewString,
[IsStzPresentation],
function(stz)
    local str;
    str := "<fp semigroup presentation with ";
    Append(str, String(Length(stz!.gens)));
    Append(str, " generator");
    if Length(stz!.gens) > 1 then
        Append(str, "s");
    fi;
    Append(str, " and ");
    Append(str, String(Length(stz!.rels)));
    Append(str, " relation");
    if Length(stz!.rels) > 1 then
        Append(str, "s");
    fi;
    Append(str, " with length ");
    Append(str, String(Length(stz)));
    Append(str, ">");
    return PRINT_STRINGIFY(str);
end);

InstallMethod(\<,
[IsStzPresentation, IsStzPresentation],
function(stz1, stz2)
    return Length(stz1) < Length(stz2);
end);

# Unnecessary? Probably
InstallMethod(Size,
[IsStzPresentation],
function(stz)
    return Length(stz);
end);
