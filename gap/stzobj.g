# Very rough attempt to create an stz object
# Labels for generators and ExtRepOfObj of relations stored as data
# Attributes give the different representations of relations
# Operations will change the presentation and output fp semigroup

DeclareOperation("StzPresentation", [IsList, IsList]);
DeclareOperation("StzPresentation", [IsFpSemigroup]);
DeclareCategory("IsStzPresentation", IsList);
#DeclareRepresentation("IsStzPresentationRep", IsStzPresentation and IsPositionalObjectRep,
#                        3);


# Can add extra representations as attributes?
# Maybe use 'representation' instead
DeclareAttribute("RelationsOfStzPresentation", IsStzPresentation);
DeclareAttribute("GeneratorsOfStzPresentation", IsStzPresentation);


InstallMethod(StzPresentation,
"for a list of generations, and a list of relations",
[IsList, IsList],
function(gens, rels)
    local out, type;

    # This is definitely the wrong way to do this
    # Not sure what "StzFamily" does but seems to work
    type := NewType(NewFamily("StzFamily", IsStzPresentation),
                    IsStzPresentation and IsAttributeStoringRep);

    # Actual underlying data
    out := rec(gens := gens, rels := rels);

    # Example
    return ObjectifyWithAttributes(out, type,
                                    RelationsOfStzPresentation, out!.rels,
                                    GeneratorsOfStzPresentation, out!.gens);
end);

InstallMethod(StzPresentation, "for a finitely presented semigroup",
[IsFpSemigroup],
function(S)
    local out, rels, type;

    type := NewType(NewFamily("StzFamily", IsStzPresentation),
                    IsStzPresentation and IsAttributeStoringRep);

    rels := List(RelationsOfFpSemigroup(S),
                x -> [ExtRepOfObj(x[1]), ExtRepOfObj(x[2])]);

    out := rec(gens := List(GeneratorsOfSemigroup(S), x -> ViewString(x)), rels := rels);

    return ObjectifyWithAttributes(out, type,
                                    RelationsOfStzPresentation, out!.rels,
                                    GeneratorsOfStzPresentation, out!.gens);
end);
