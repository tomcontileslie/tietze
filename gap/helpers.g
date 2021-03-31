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
  return rec(gens := List(gens, ViewString), rels := rels);
end;

# This function takes an stz rep and returns the FpSemigroup corresponding to it
#
# Argument <stz> should be a record with stz.gens a list of strings, and
# stz.rels a list of pairs of assoc words
StzObjToFpSemigroup := function(stz)
  local f, fam, rels;
  f := FreeSemigroup(stz.gens);
  # retrieve family for assoc word transplant
  fam := FamilyObj(f.1);
  # convert word reps into free semigroup elements
  rels := List(stz.rels, x -> List(x, y -> AssocWordByLetterRep(fam, y)));
  # quotient out to get the fp semigroup
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

# This function takes as argument a list of strings representing generator
# names, e.g. from a free semigroup. It returns a string that is "reasonable"
# as a new variable name, that is not already taken.
NewGeneratorName := function(names)
  local alph, Alph, na, nA, names_prefx, names_suffx, int_positions, prefixes,
        prefixes_collected, p, ints, i, name;

  # useful helper variables
  alph := "abcdefghijklmnopqrstuvwxyz";
  Alph := "ABCDEFGHIJKLMNOPQRSTUVWXYZ";

  # SPECIAL CASE 0: empty list
  if Length(names) = 0 then
    return "a";
  fi;

  # SPECIAL CASE 1: only one generator
  if Length(names) = 1 then
    if Length(names[1]) = 1 then
      if names[1][1] in Alph then
        return [First(Alph, x -> not [x] in names)];
      elif names[1][1] in alph then
        return [First(alph, x -> not [x] in names)];
      else
        return "a";
      fi;
    else
      return "a";
    fi;
  fi;

  # SPECIAL CASE 2: single letter names are present. Add an unused letter
  # with the most common capitalisation
  na := Length(Filtered(names, x -> Length(x) = 1 and x[1] in alph));
  nA := Length(Filtered(names, x -> Length(x) = 1 and x[1] in Alph));
  if 2 <= na and na < 26 then
    if na <= nA and nA < 26 then
      return [First(Alph, x -> not [x] in names)];
    else
      return [First(alph, x -> not [x] in names)];
    fi;
  elif 2 <= nA and nA < 26 then
    return [First(Alph, x -> not [x] in names)];
  fi;

  # SPECIAL CASE 3: there are names like s1, s3, s23, etc or x12, etc
  names_prefx := StructuralCopy(names);
  names_suffx := StructuralCopy(names);
  Apply(names_prefx, x -> [x[1]]);
  for name in names_suffx do
    Remove(name, 1);
  od;
  int_positions := PositionsProperty(names_suffx, x -> Int(x) <> fail
                                              and x <> ""
                                              and x[1] <> '-');
  if Length(int_positions) >= 2 then
    prefixes           := names_prefx{int_positions};
    prefixes_collected := Collected(prefixes);
    # look for highest frequency in collected list
    p := prefixes_collected[PositionMaximum(prefixes_collected, x -> x[2])][1];
    # find maximum suffix int, even amongst those with prefix not p
    ints := List(names_suffx{int_positions}, Int);
    i    := Maximum(ints) + 1;
    return Concatenation(p, String(i));
  fi;

  # if none of the special cases are covered, just try s1, s2,... until good
  for i in [1 .. Length(names) + 1] do
    if not Concatenation("s", String(i)) in names then
      return Concatenation("s", String(i));
    fi;
  od;
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
  local gens, rels, newRels, rel1, rel2, i;
    # Using format of LetterRepAssocWord, can change
    # Global variable eg STZ_GENS := 1, STZ_RELS := 2?
    gens := stzObj.gens;  # TDCL: note this is unused
    rels := stzObj.rels;

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
  local out, pos, i;
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
