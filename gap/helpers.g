## helpers.g: Semigroup Tietze Helper functions
##
## The goal of this file is to implement some standard "tietze-compatible"
## presentation format, and then implement low-level methods that substitute
## out words and generators for other generators.
##
## Choose list of relations format similar to Letter Rep.
## Throughout, <stz> will be a record with the following components:
## - stz.gens is a list of generators of the fp semigroup
## - stz.rels is list of lists of LetterRep ints, where [1, 2, 2] denotes abb.

# This function takes an FpSemigroup and returns its stz rep
FpSemigroupToStzObj := function(s)
  local gens, rels;
  if not IsFpSemigroup(s) then
    ErrorNoReturn("Argument <s> must be a fp semigroup");
  fi;
  gens := GeneratorsOfSemigroup(s);
  rels := List(RelationsOfFpSemigroup(s),
               x -> [LetterRepAssocWord(x[1]),
                     LetterRepAssocWord(x[2])]);
  return rec(gens := gens, rels := rels);
end;

# This function takes an stz rep and returns the FpSemigroup corresponding to it
# (note the generators in stz.gens are generators of *some* fp semigroup,
# but they are not the generators of the fp semigroup that will be output
# because the presentation has changed compared to when the stz object was
# created
#
# Essentially this function is just GAP gymnastics
StzObjToFpSemigroup := function(stz)
  local f, fam, rels;
  # retrieve overlying free semigroup
  f := FreeSemigroupOfFpSemigroup(
       FpGrpMonSmgOfFpGrpMonSmgElement(stz.gens[1]));
  fam  := FamilyObj(f.1);
  # convert relations into free semigroup relations
  rels := List(stz.rels,
               x -> [AssocWordByLetterRep(fam, x[1]),
                     AssocWordByLetterRep(fam, x[2])]);
  return f / rels;
end;

# This function merges any repeated generators in an ExtRep list.
# N.B. assumes list of pos ints as input.
# This should be used whenever creating an ExtRep that is not guaranteed to
# be as simple as possible.
StzSimplify := function(ext)
  local n, last, out, i;
  # length of ext must be even, generators in odd positions
  n := Length(ext);

  # reconstruct list but if the same generator appears twice in a row, add the
  # powers
  last := fail;
  out  := [];
  for i in [1, 3 .. n - 1] do
    if ext[i] = last then
      out[Length(out)] := out[Length(out)] + ext[i + 1];
    else
      Append(out, [ext[i], ext[i + 1]]);
    fi;
    last := ext[i];
  od;
  return out;
end;

# This function takes an ExtRep and substitutes a relation of the form
# generator = ExtRep(product of other generators), e.g. 3 = [2, 1, 1, 4].
StzSubstitute := function(ext, gen, prod)
  local n, out, i, j;
  # length of ext must be even since an ext rep; generators in odd positions.
  n := Length(ext);

  # reconstruct the list, iterating over pairs of entries at a time,
  # but swap out each occurrence of gen for prod.
  out := [];
  for i in [1, 3 .. n - 1] do
    if ext[i] = gen then
      # append prod as many times as the power of gen we're removing
      for j in [1 .. ext[i + 1]] do
        Append(out, prod);
      od;
    else
      # this is just a normal generator so append it and its power
      Append(out, [ext[i], ext[i + 1]]);
    fi;
  od;
  return StzSimplify(out);
end;

########
# TCL: todo: all the functions above work on ExtRep objects. Functions
# below work on LetterRep objects. LetterRep is preferable, so the
# ones above need to be updated.
########

# Searches through the relations of stzObj and replaces each instance of subword
# with newWord, except if the entire relation is exactly subWord (preserving a
# newly created relation)
# newWord should be stricly less than subword or else may be an infinite
# sequence (maybe just handle this?)
StzReplaceSubword := function(stzObj, subword, newWord)
    local out, gens, rels, newRels, rel1, rel2;
    # Using format of LetterRepAssocWord, can change
    # Global variable eg STZ_GENS := 1, STZ_RELS := 2?
    gens := stzObj[1];
    rels := StzObj[2];

    newRels := List([1 .. Length(rels)], x -> []);
    for i in Length(rels) do
        if rels[i][1] = subword then
            rel1 := rels[i][1];
        else
            rel1 := StzReplaceSubwordRel(rels[i][1], subword, newWord);
        fi;
        if rels[i][2] = subword then
            rel2 := rels[i][2];
        else
            rel2 := StzReplaceSubwordRel(rels[i][2], subword, newWord);
        fi;
        newRels[i] := [rel1, rel2];
    od;
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
