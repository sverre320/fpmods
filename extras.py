
# *****************************************************************************
#       Copyright (C) 2022 Sverre Lunøe-Nielsen <sverreal@uia.no>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.modules.fp_graded.steenrod.module import SteenrodFPModule
from sage.modules.fp_graded.steenrod.homspace import SteenrodFPModuleHomspace
from sage.modules.fp_graded.steenrod.morphism import SteenrodFPModuleMorphism

from sage.categories.homset import Hom

def direct_sum(modules):
    r'''

    Form the direct sum of the given modules.

    INPUT:

    - ``modules`` -- An iterable of SteenrodFPModules.

    OUTPUT:

    - ``i`` -- An array of injective homomorphisms into the direct sum,
      one for each of the summands.

    - ``p`` -- An array of projections from the direct sum onto the
      factors of the direct sum.

    EXAMPLES::
        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [0], [[Sq(1)], [Sq(2)]])
        sage: injs, projs = direct_sum([M,M])
        sage: # p1 is the projection $M\oplus M \to M$ onto the first summand:
        sage: p1 = projs[0]
        sage: M_plus_M = p1.domain()
        sage: M_plus_M
        Finitely presented left module on 2 generators and 4 relations over mod 2 Steenrod algebra, milnor basis

    '''
    if len(modules) == 0:
        raise ValueError('No modules to sum.')

    alg = modules[0].base_ring()
    for mod in modules:
        if mod.base_ring() != alg:
            raise ValueError('Modules must be defined over the same algebra.')

    gens = [mod.generator_degrees() for mod in modules]
    nums = [len(gs) for gs in gens]

    def pad(r, i):
        a = sum(nums[0:i])
        b = sum(nums[i+1:])
        return (0,)*a + tuple(r) + (0,)*b

    sss = [ [ pad(r.coefficients(), i) for r in mod.relations()] for i, mod in enumerate(modules)]
    rels = sum( sss , [])

    # This is the direct sum as an FPA_Module:
    sum_ = SteenrodFPModule(alg, sum(gens, ()), rels)
    generator_elements = sum_.generators()

    # Create the canonical injection
    injections = [ Hom(mod, sum_)(generator_elements[sum(nums[0:i]):sum(nums[0:i+1])]) for i,mod in enumerate(modules) ]

    # Create the canonical projections
    projections = [ Hom(sum_, mod)([mod.zero()]*sum(nums[0:i]) + list(mod.generators()) + [mod.zero()]*sum(nums[i+1:])) for i,mod in enumerate(modules) ]

    return injections, projections



