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
from sage.rings.integer import Integer
from sage.categories.homset import Hom
from sage.modules.free_module import VectorSpace


def margolis_homology(M, n, a):
    r'''
    Compute the Margolis homology in the given internal degree with
    respect to the given operation.

    INPUT:

    - ``M`` -- A SteenrodFPModule.

    - ``n`` -- The Internal module degree.

    - ``a`` -- A Steenrod operation.  This function fails if a*a != 0.

    OUTPUT:

    - ``H`` -- The vectorspace quotient `\ker(a)/\im(a)`, i.e. the homology
      of the chain complex `M[n-q] \to M[n] \to M[n+q]`, where `q` is the
      degree of `a`, and the maps are given by the action of `a`.
    
    - ``k`` -- A list of elements of M[n] which is a basis for the kernel.

    - ``i`` -- A list of elements if M[n] which is a basis for the image.

    EXAMPLES::

        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [0], [[Sq(2)]])
        sage: margolis_homology(M, n=11, a=Sq(1))
        (Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
         V: Vector space of degree 3 and dimension 2 over Finite Field of size 2
         Basis matrix:
         [1 0 1]
         [0 1 0]
         W: Vector space of degree 3 and dimension 1 over Finite Field of size 2
         Basis matrix:
         [0 1 0],
         [(Sq(4,0,1)+Sq(8,1))*g[0]],
         [Sq(5,2)*g[0]])

    '''
    if a*a != 0:
        raise ValueError(f'The operation: {a} satisfies: {a}*{a}={a*a}, which is non-zero.')
    deg = a.degree()

    U = M.vector_presentation(n-deg)
    V = M.vector_presentation(n)
    W = M.vector_presentation(n+deg)

    f_images = [(a*x).vector_presentation() for x in M.basis_elements(n)]
    f_images = [x if x != None else (0,)*W.dimension() for x in f_images]
    f = Hom(V,W)(f_images)

    g_images = [(a*x).vector_presentation() for x in M.basis_elements(n-deg)]
    g_images = [x if x != None else (0,)*V.dimension() for x in g_images]
    g = Hom(U,V)(g_images)

    k = f.kernel()
    c = g.image()

    H = k.quotient(c)
    kernel_basis = [M.element_from_coordinates(H.lift(v), n) for v in H.basis()]
    image_basis = [M.element_from_coordinates(b, n) for b in H.W().basis()]

    return H, kernel_basis, image_basis

