## stz.g: Semigroup Tietze
##
## The goal of this file is to implement some standard "tietze-compatible"
## presentation format, and then implement simplification methods.
##
## Choose list of relations format similar to ExtRepOfObj. Throughout, <stz>
## will be a list of lists of ints, where [1, 4, 2, 3] denotes a^4 * b^3.

# This function takes an FpSemigroup and returns its stz.
AsStzObject := function(s)
  if not IsFpSemigroup(s) then
    ErrorNoReturn("Argument <s> must be a fp semigroup");
  fi;
  return List(RelationsOfFpSemigroup(s),
              x -> [ExtRepOfObj(x[1]), ExtRepOfObj(x[2])]);
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
