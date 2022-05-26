
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

from sage.rings.integer import Integer
from sage.categories.homset import Hom
from sage.categories.morphism import Morphism as SageMorphism
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

from sage.categories.homset import Homset
from sage.modules.free_module import VectorSpace

# This function is injected into the SteenrodFPModuleHomspace class:
# SteenrodFPModuleHomspace.vector_presentation = _vector_presentation
def _vector_presentation(self, n=0):
    r'''

    Return a vectorspace over the ground field isomorphic to the
    vectorspace of `A`-linear homomorphisms of degree `n` belonging
    to this homspace.

    INPUT:

    - ``n`` -- An integer degree.

    OUTPUT:
    A vectorspace.

    .. NOTE::

        This function is injected into the SteenrodFPModuleHomspace class:
        SteenrodFPModuleHomspace.vector_presentation = _vector_presentation

        Therefore, the `self` variable is a reference to a homspace
        class of maps between two fp. modules.

    EXAMPLES::

        sage: from sage.modules.fp_graded.steenrod.module import SteenrodFPModule

        sage: A1 = SteenrodAlgebra(2, profile=(2,1))
        sage: M = SteenrodFPModule(A1, [0], [[A1.Sq(2)]])
        sage: Hom(M.suspension(3), M).vector_presentation(0)
        Vector space of dimension 1 over Finite Field of size 2

    '''
    k = self.base_ring().base_ring()
    return VectorSpace(k, len(self.basis_elements(n)))


# This function is injected into the SteenrodFPModuleHomspace class:
# SteenrodFPModuleHomspace.morphism_from_coordinates = _morphism_from_coordintes
def _morphism_from_coordintes(self, coordinates, n=0):
    r'''

    Return a homomorphism of this homspace.

    INPUT:

    - ``coordinates`` -- A vector of coefficients in the ground field.

    - ``n`` -- An integer degree.

    OUTPUT:

    The linear combination of morphisms given by the ``coordinates`` and
    the basis for the degree ``n`` morphisms of this homspace given by
    ``self.basis_elements()``.

    .. NOTE::

        This function is injected into the SteenrodFPModuleHomspace class:
        SteenrodFPModuleHomspace.morphism_from_coordinates = _morphism_from_coordintes

        Therefore, the `self` variable is a reference to a homspace
        class of maps between two fp. modules.

    EXAMPLES::

        sage: from sage.modules.fp_graded.steenrod.module import SteenrodFPModule
        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [0], [[Sq(1)], [Sq(2)]])
        sage: N = SteenrodFPModule(A, [0], [[Sq(2)]])
        sage: # The set of graded A-linear homomorphisms M -> N
        sage: hom = Hom(M,N)

        sage: # The vectorspace of all degree 18 homomorphisms turns out to have dimension 2:
        sage: hom.vector_presentation(n=18)
        Vector space of dimension 2 over Finite Field of size 2
    
        sage: # Given coordinates, we can find the homomorphism it represents
        sage: coordinates = (1,0)
        sage: f = hom.morphism_from_coordinates(coordinates, n=18)
        sage: print(f)
        Module morphism:
          From: Finitely presented left module on 1 generator and 2 relations over mod 2 Steenrod algebra, milnor basis
          To:   Finitely presented left module on 1 generator and 1 relation over mod 2 Steenrod algebra, milnor basis
          Defn: g[0] |--> Sq(0,1,0,1)*g[0]

    '''

    basis = self.basis_elements(n)

    if len(basis) != len(coordinates):
        raise ValueError(f'The coordinate vector has an incorrect dimension. ' +
                         'It should be {len(basis)}.')
    return sum([Integer(c)*f for c,f in zip(coordinates, basis)])


# This function is injected into the SteenrodFPModuleHomspace class:
# SteenrodFPModuleHomspace.morphism_to_coordinates = _morphism_to_coordinates
def _morphism_to_coordinates(self, f):
    r"""

    INPUT:

    - ``f`` -- A homomorphism of SteenrodFPModules belonging to ``self``.

    OUTPUT:
    The coefficient vector for 'f` with respect to the basis given
    by ``self.basis_elements()``.

    .. NOTE::
    
        This function is injected into the SteenrodFPModuleHomspace class:
        SteenrodFPModuleHomspace.morphism_to_coordinates = _morphism_to_coordinates

        Therefore, the `self` variable is a reference to a homspace
        class of maps between two fp. modules.

    EXAMPLES::

        sage: from sage.modules.fp_graded.steenrod.module import SteenrodFPModule
        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [0], [[Sq(2)]])
        sage: hom = Hom(M.suspension(7), M)
        sage: f = hom.an_element(7); f
        Module morphism:
          From: Finitely presented left module on 1 generator and 1 relation over mod 2 Steenrod algebra, milnor basis
          To:   Finitely presented left module on 1 generator and 1 relation over mod 2 Steenrod algebra, milnor basis
          Defn: g[7] |--> (Sq(1,2,1)+Sq(4,1,1))*g[0]
        sage: hom.morphism_to_coordinates(f)
        (1,)

    """
    if not f in self:
        raise ValueError('The given morphism does not belong to this homspace.')

    M = self.domain()
    N = self.codomain()

    if f.is_zero():
        return None # the zero map has no degree, and therefore we don't know what its codomain is.
    elif M.is_trivial() or N.is_trivial():
        return self.zero()

    k = M.base_ring().base_ring()
    coords = []
    if not M.has_relations():
        # Fast track for source modules that are free
        for i, g in enumerate(M.generators()):
            v = f(g).vector_presentation()

            # As always, treat the zero value ad hoc..
            if v is None:
                v = len(N[f.degree() + g.degree()]) * (0,)

            coords += v
        return tuple(coords)
    else:
        def _vecpres(morphism, element):
            y = morphism(element)
            if y.is_zero():
                k_ = len(morphism.codomain()[morphism.degree() + element.degree()])
                return (0,)*k_
            return tuple(y.vector_presentation())

        # When the source module has relations, we need to do a little linear algebra.
        phis = self.basis_elements(f.degree())
        columns_ = [ [_vecpres(phi, b) for b in M.generators()] for phi in phis]
        columns = [ sum(xx, ()) for xx in columns_]
        mat = matrix(k, columns)
        v = sum([_vecpres(f,b) for b in M.generators()], ())
        return tuple(mat.solve_left(vector(v)))


# Inject methods into ``SteenrodFPModuleMorphism``
# SteenrodFPModuleMorphism.homspace_map_by_precomposition = _homspace_map_by_precomposition
def _homspace_map_by_precomposition(self, Q):
    r'''

    Create a linear homomorphism between the graded vectorspace
    homspaces of homspaces.

    Let `f` be the ``self`` homomorphism with source `M` and target
    module `N`.  Then we create the linear transformation
    `f^* : hom(M,Q) \to hom(N,Q)`.

    INPUT:
    
    - ``Q`` -- A SteenrodFPModule.

    OUTPUT:
    The linear homomorphism `f^* : hom(M,Q) \to hom(N,Q)`.

    .. NOTE::
    
        This function is injected into the SteenrodFPModuleMorphism class:
        SteenrodFPModuleMorphism.homspace_map_by_precomposition = _homspace_map_by_precomposition

        Therefore, the `self` variable is a reference to a morphism
        between two fp. modules.

    EXAMPLES::

        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [0], [[Sq(2)]])
        sage: N = SteenrodFPModule(A, [7], [[Sq(1)]])
        sage: C = SteenrodFPModule(A, [0], [[Sq(4)+Sq(2)*Sq(2)]])
        sage: hom1 = Hom(M, C)
        sage: hom2 = Hom(N, C)
        sage: f = Hom(N, M).an_element()
        sage: f.is_zero()
        False
        sage: T = f.homspace_map_by_precomposition(C)
        sage: T.vector_presentation(3)
        Vector space morphism represented by the matrix:
        [1 0]
        Domain: Vector space of dimension 1 over Finite Field of size 2
        Codomain: Vector space of dimension 2 over Finite Field of size 2

    '''
    M = self.domain()
    N = self.codomain()
    homhom = FPHomspaceMorphismHomspace( Hom(N, Q), Hom(M, Q) )
    return homhom.precompose(self)


def cohomology(f, g, N, t):
    r'''
    
    Compute the cohomology of `f` and `g` with coeffients in `N`.

    The given two maps `f` and `g` are assumed to be composable
    and form a chain complex
    $$
    f: R\to S` and `g: S\to T`.
    $$

    Then this function computes
    $$
    \hom^t(T, N) \to \hom^t(S, N) \to \hom^t(R, N)
    $$
    in degree ``t`` as a quotient vectorspace.

    INPUT:

    - ``f`` -- Homomorphism of SteenrodFPModules `R \to S`.

    - ``g`` -- Homomorphism of SteenrodFPModules `S \to T`.

    - ``N`` -- SteenrodFPModule.

    - ``t`` -- (cohomologically) degree.

    OUTPUT:

    - ``V`` -- A quotient vectorspace.

    - ``bas`` -- A set of cocycles `S\to N` which form a basis for ``V``.

    .. NOTE::

        This function uses the cohomological degree convention
        and considers a map of degree `t` to be a map which lowers
        degrees by `t`.

    EXAMPLES::

        sage: A1 = SteenrodAlgebra(2, profile=(2,1))
        sage: F2 = SteenrodFPModule(A1, [0], [[Sq(1)], [Sq(2)]])
        sage: res = F2.resolution(5, verbose=False)
        sage: H, bas = cohomology(res[5], res[4], F2, 12)
        sage: H
        Vector space quotient V/W of dimension 1 over Finite Field of size 2 where
        V: Vector space of degree 1 and dimension 1 over Finite Field of size 2
        Basis matrix:
        [1]
        W: Vector space of degree 1 and dimension 0 over Finite Field of size 2
        Basis matrix:
        []
        sage: bas
        [Module morphism:
           From: Free graded left module on 3 generators over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
           To:   Finitely presented left module on 1 generator and 2 relations over sub-Hopf algebra of mod 2 Steenrod algebra, milnor basis, profile function [2, 1]
           Defn: g[4] |--> 0
                 g[8] |--> 0
                 g[12] |--> g[0]]

    '''

    if not f.codomain() is g.domain():
        raise ValueError('The homomorphisms are not composable.')
    if not (g*f).is_zero():
        raise ValueError('The homomorphisms do not form a chain complex.')

    f_ = f.homspace_map_by_precomposition(N)
    hom_S_N = f_.domain()
    f_lin = f_.vector_presentation(-t)
    ker = f_lin.kernel()

    g_ = g.homspace_map_by_precomposition(N)
    g_lin = g_.vector_presentation(-t)
    im = g_lin.image()

    coho = ker.quotient(im)

    kernel_basis = [hom_S_N.morphism_from_coordinates(coho.lift(v), -t) for v in coho.basis()]
    # Do we care about a basis for the image?
    # image_basis = [hom_S_N.element_from_coordinates(coho.lift(v), -t) for v in im.basis()]
    return (coho, kernel_basis)


def ext(res, N, s, t):
    r'''

    Compute cohomology of the cochain complex formed by applying
    `hom(-, N)` on the given resolution ``res``.
    
    INPUT:

    - ``res`` -- Free resolution of an SteenrodFPModule M.

    - ``N`` -- A SteenrodFPModule coefficient module.

    - ``s`` -- Cohomological degree.

    - ``t`` -- Internal degree.

    OUTPUT:

    The dimension of `Ext^{s,t}(M, N)` as an `\F_p` vectorspace.

    EXAMPLES::

        sage: A1 = SteenrodAlgebra(2, profile=(2,1))
        sage: F2 = SteenrodFPModule(A1, [0], [[Sq(1)], [Sq(2)]])
        sage: res = F2.resolution(10, verbose=False)
        sage: ext(res, F2, 2, 4)
        1

    '''

    if s == 0:
        # Cohomological degree zero
        Z = SteenrodFPModule(N.base_ring(),[]) # Zero module
        zeromap = Hom(res[0].domain(), Z).zero()
        H, bas = cohomology(res[1], zeromap, N, t)
    else:
        H, bas = cohomology(res[s+1], res[s], N, t)

    return H.dimension()


class FPHomspaceMorphism(SageMorphism):

    r'''

    A class for modelling morphisms between homspaces of SteenrodFPModules.

    EXAMPLES::

        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [7], [[Sq(2)]])
        sage: N = SteenrodFPModule(A, [0], [[Sq(2)], [Sq(3)]])
        sage: C = SteenrodFPModule(A, [-12], [[Sq(4)+Sq(2)*Sq(2)]])

    Choose a non-trivial map M -> N::
        sage: f = Hom(M, N).an_element()
        sage: f.is_zero()
        False

    Use precomposition to create a map of hom-spaces of homspaces::
        sage: homhom = FPHomspaceMorphismHomspace( Hom(N, C), Hom(M, C) )
        sage: T = homhom.precompose(f)
        sage: T.domain() is Hom(N, C)
        True
        sage: T.codomain() is Hom(M, C)
        True
        sage: T.vector_presentation(7)
        Vector space morphism represented by the matrix:
        [0 1 0 0]
        [0 0 1 0]
        Domain: Vector space of dimension 2 over Finite Field of size 2
        Codomain: Vector space of dimension 4 over Finite Field of size 2

    '''

    def __init__(self, parent, morphism):
        r'''

        Create a homomorphism between homspaces of finitely
        presented graded modules.

        INPUT:

        - ``parent`` -- The instance of the homset this morphism belongs to.
        
        - ``morphism`` -- A morphism that transforms morphisms of one homset
          to another.


        .. NOTE::
           We are very often interested in creating morphisms
           $$
               \hom(N,C) \to \hom(M,C)
           $$
           or 
           $$
               \hom(M,N) \to \hom(M,C)
           $$
           by pre- or post-composing with maps.   In this situation,
           use the ``precompose`` and ``postcompose`` methods of the parent
           class ``FPHomspaceMorphismHomspace``.

        '''

        # Call the base class constructor.
        SageMorphism.__init__(self, parent)

        self.morphism = morphism

        
    def __call__(self, f):
        r'''

        INPUT:

        - ``f`` -- A morphism belonging to self.domain().

        OUTPUT:

        A morphism belonging to self.codomain().

        '''
        return self.morphism(f)
        

    def vector_presentation(self, n):
        r'''

        INPUT:

        - ``n`` -- The degree of the graded transformation we want to
          get a vectorspace representation of.

        OUTPUT:
        A linear transformation of vectorspaces.

        EXAMPLES::

            sage: A = SteenrodAlgebra(2)
            sage: M = SteenrodFPModule(A, [7], [[Sq(2)]])
            sage: N = SteenrodFPModule(A, [0], [[Sq(2)], [Sq(3)]])
            sage: C = SteenrodFPModule(A, [-12], [[Sq(4)+Sq(2)*Sq(2)]])
    
        Choose a non-trivial map M -> N::
            sage: f = Hom(M, N).an_element()
            sage: f.is_zero()
            False
    
        Use precomposition to create a map of hom-spaces of homspaces::
            sage: homhom = FPHomspaceMorphismHomspace( Hom(N, C), Hom(M, C) )
            sage: T = homhom.precompose(f)
            sage: T.domain() is Hom(N, C)
            True
            sage: T.codomain() is Hom(M, C)
            True
            sage: T.vector_presentation(7)
            Vector space morphism represented by the matrix:
            [0 1 0 0]
            [0 0 1 0]
            Domain: Vector space of dimension 2 over Finite Field of size 2
            Codomain: Vector space of dimension 4 over Finite Field of size 2
        
        '''
        source = self.parent().domain() # The homspace we map from
        target = self.parent().codomain() # The homspace we map to
        U = source.vector_presentation(n)
        V = target.vector_presentation(n)
        values = [target.morphism_to_coordinates(
            self.morphism(basis_func)) for basis_func in source.basis_elements(n)]
        k_ = V.dimension()
        values = [(0,)*k_ if x is None else x for x in values]

        return Hom(U, V)(values)


class FPHomspaceMorphismHomspace(Homset):
    r'''

    The set of linear maps `M \to N` between two finitely presented
    graded modules can be given the structure of a graded vectorspace.

    This class implements the Sage ``homset`` of maps of such homsets.

    .. NOTE::
    
        Sage's free function ``Hom`` has not been changed to recognize
        homsets of fp. modules as parent modules themselves.  This
        means that to create an instance of this class, the class
        constructor must be called explicitly like in the following
        examples.

    EXAMPLES::

        sage: A = SteenrodAlgebra(2)
        sage: M = SteenrodFPModule(A, [7], [[Sq(2)]])
        sage: N = SteenrodFPModule(A, [0], [[Sq(2)], [Sq(3)]])
        sage: C = SteenrodFPModule(A, [-12], [[Sq(4)+Sq(2)*Sq(2)]])

    Choose a non-trivial map M -> N::
        sage: f = Hom(M, N).an_element()
        sage: f.is_zero()
        False

    Use precomposition to create a map of hom-spaces of homspaces::
        sage: homhom = FPHomspaceMorphismHomspace( Hom(N, C), Hom(M, C) )

    The 
        sage: T = homhom.precompose(f)
        sage: T.domain() is Hom(N, C)
        True
        sage: T.codomain() is Hom(M, C)
        True
        sage: T.vector_presentation(7)
        Vector space morphism represented by the matrix:
        [0 1 0 0]
        [0 0 1 0]
        Domain: Vector space of dimension 2 over Finite Field of size 2
        Codomain: Vector space of dimension 4 over Finite Field of size 2

    '''


    def precompose(self, f):
        r'''
        Create a morphism of homspaces by precomposition.

        INPUT:

        - `f` -- A homomorphism.

        OUTPUT:

        The linear homomorphism of homspaces induced by precomposing with `f`.


        EXAMPLES::
    
            sage: A = SteenrodAlgebra(2)
            sage: M = SteenrodFPModule(A, [7], [[Sq(2)]])
            sage: N = SteenrodFPModule(A, [0], [[Sq(2)], [Sq(3)]])
            sage: C = SteenrodFPModule(A, [-12], [[Sq(4)+Sq(2)*Sq(2)]])
    
        Choose a non-trivial map M -> N::
            sage: f = Hom(M, N).an_element()
            sage: f.is_zero()
            False
    
        Use precomposition to create a map of hom-spaces of homspaces::
            sage: homhom = FPHomspaceMorphismHomspace( Hom(N, C), Hom(M, C) )
            sage: T = homhom.precompose(f)
            sage: T.domain() is Hom(N, C)
            True
            sage: T.codomain() is Hom(M, C)
            True
            sage: T.vector_presentation(7)
            Vector space morphism represented by the matrix:
            [0 1 0 0]
            [0 0 1 0]
            Domain: Vector space of dimension 2 over Finite Field of size 2
            Codomain: Vector space of dimension 4 over Finite Field of size 2
        '''
        if not f.codomain() is self.domain().domain():
            raise ValueError('The codomain of the homomorphism to precompose '+
                             'with must equal the domain of this homspace.')
        if not f.is_zero() and f.degree() != 0:
            raise ValueError('The homomorphism must be of degree zero.')
        return FPHomspaceMorphism(self, lambda h: h*f)


    def postcompose(self, f):
        r'''
        Create a morphism of homspaces by postcomposition.

        INPUT:

        - `f` -- A homomorphism.

        OUTPUT:

        The linear homomorphism of homspaces induced by postcomposing with `f`.

        EXAMPLES::
    
            sage: A = SteenrodAlgebra(2)
            sage: M = SteenrodFPModule(A, [7], [[Sq(2)]])
            sage: N = SteenrodFPModule(A, [0], [[Sq(2)], [Sq(3)]])
            sage: C = SteenrodFPModule(A, [-12], [[Sq(4)+Sq(2)*Sq(2)]])
    
        Choose a non-trivial map M -> N::
            sage: f = Hom(M, N).an_element()
            sage: f.is_zero()
            False
    
        Use postcomposition to create a map of hom-spaces of homspaces::
            sage: homhom = FPHomspaceMorphismHomspace( Hom(N, C), Hom(M, C) )
            sage: T = homhom.precompose(f)
            sage: T.domain() is Hom(N, C)
            True
            sage: T.codomain() is Hom(M, C)
            True
            sage: T.vector_presentation(7)
            Vector space morphism represented by the matrix:
            [0 1 0 0]
            [0 0 1 0]
            Domain: Vector space of dimension 2 over Finite Field of size 2
            Codomain: Vector space of dimension 4 over Finite Field of size 2
        
        '''
        if not f.domain() is self.domain().codomain():
            raise ValueError('The codomain of the homomorphism to precompose ' +
                             'with must equal the domain of this homspace.')
        if not f.is_zero() and f.degree() != 0:
            raise ValueError('The homomorphism must be of degree zero.')
        return FPHomspaceMorphism(self, lambda h: f*h)


# Inject methods into ``SteenrodFPNModuleHomspace``
SteenrodFPModuleHomspace.vector_presentation = _vector_presentation
SteenrodFPModuleHomspace.morphism_from_coordinates = _morphism_from_coordintes
SteenrodFPModuleHomspace.morphism_to_coordinates = _morphism_to_coordinates

# Inject methods into ``SteenrodFPNModuleMorphism``
SteenrodFPModuleMorphism.homspace_map_by_precomposition = _homspace_map_by_precomposition


