using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.CompactGroups;

internal sealed class MatrixCoefficientDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/CompactGroups/MatrixCoefficientDensity.";
    private static LibraryNoteRef PeterWeyl => LibraryNoteRef.Create("D5/L/LieTheory/peterweyl1927vollstaendigkeit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a compact topological group G, the complex linear span of the matrix coefficients of the continuous homomorphisms from G into the unitary groups of finite degree is dense in the space of continuous complex functions on G.",
        H("Density of Matrix Coefficients of Unitary Representations of Compact Groups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("matrix-coefficient-density-dense-span"),
                DeclarationHandle.Create(Prefix + "dense_span_unitary_coefficients"),
                H("Matrix coefficients span a dense subspace of the continuous functions"),
                StatementSource.FromAuthor(DensityFormula()),
                AssessedProvenance.FromRepo(PeterWeyl),
                Blocks(
                    Paragraph(Text("Let G be a compact topological group; no separation axiom is assumed. For a natural number n, a continuous group homomorphism r from G into the group U(n) of unitary n x n complex matrices, written unitaryGroup(Fin(n), C), and indices i and j in Fin(n), the function sending g to r(g)_{i,j}, the entry in row i and column j of the matrix r(g), is a continuous complex function on G, called a matrix coefficient of r. The theorem states that the complex linear span of the set of all such functions, taken over all n, all r and all i and j, is dense in the space C(G, C) of continuous complex functions on G. In the formula the set consists of the functions f in C(G, C) for which there are n, r, i and j with f(g) = r(g)_{i,j} for every g in G; span(C, S) is the complex linear span of S, and Dense refers to its underlying set. The topology of C(G, C) is the compact-open topology, which for compact G is the topology of uniform convergence, so every continuous complex function on G is a uniform limit of finite complex linear combinations of matrix coefficients. This is the classical approximation theorem of Peter and Weyl.")),
                    Paragraph(Text("The span is closed under multiplication and complex conjugation and contains the constant function 1. The constant 1 is the coefficient of the trivial homomorphism into U(1). If r takes values in U(n) and s in U(m), then the Kronecker product of r(g) and s(g) is a unitary matrix of size nm, it is multiplicative and continuous in g, and its entries are the products r(g)_{i,j} s(g)_{k,l}; after the pairs of indices are numbered by Fin(nm), this is a homomorphism into U(nm) whose coefficients are the products of coefficients of r and s. The entrywise complex conjugate of r(g) is again unitary and multiplicative, so the complex conjugate of a coefficient of r is a coefficient of a homomorphism into U(n). By bilinearity the span is therefore a unital subalgebra of C(G, C) closed under complex conjugation.")),
                    Paragraph(Text("Let Q be the separation quotient of G, obtained by identifying points that have the same neighbourhoods, and let mk be the quotient map from G onto Q. Then Q is a compact topological group in which points are closed, and mk is a continuous surjective homomorphism. For distinct points x and y of Q the complement of the point x y^(-1) is an open neighbourhood of the identity, so by the theorem on small kernels of unitary representations of compact groups there is a continuous homomorphism r from Q into some U(n) with r(x y^(-1)) not equal to 1. Then r(x) and r(y) differ in some entry (i, j), and the coefficient sending q to r(q)_{i,j} separates x from y; its composite with mk is the coefficient of the homomorphism r composed with mk on G. Hence the functions h in C(Q, C) whose composite with mk lies in the span form a subalgebra closed under conjugation that separates the points of the compact Hausdorff space Q, and the complex Stone-Weierstrass theorem makes it dense in C(Q, C).")),
                    Paragraph(Text("Composition with mk is a continuous map from C(Q, C) to C(G, C), and it is surjective: a continuous function into the Hausdorff space C takes equal values at points with the same neighbourhoods, so it factors through Q by a continuous function. The image of a dense set under a continuous surjection is dense, and the image of the subalgebra above lies in the span, so the span is dense in C(G, C). When G carries the indiscrete topology the continuous complex functions on G are the constants, which are the coefficients of the trivial representation, in accordance with the absence of a separation axiom.")),
                    Paragraph(Text("Compactness of G cannot be dropped. In the group of affine maps x to a x + b of the real line with a positive, the restriction of a continuous finite-dimensional unitary representation to the translations is a continuous unitary representation of the real line, hence a sum of characters sending b to exp(i c b) for finitely many real frequencies c. Conjugating the translation by b with the dilation by a gives the translation by a b, so this finite set of frequencies is invariant under multiplication by every positive a and consists of 0 alone; every such representation is therefore trivial on the translations. All matrix coefficients then take equal values at the identity and at the translation by 1, and so does every function in the closure of their span for the compact-open topology, while the continuous function sending the map x to a x + b to the number b takes the values 0 and 1 there.")),
                    Paragraph(Text("The statement is the uniform density form of the theorem. It does not give density of matrix coefficients in the Lebesgue spaces of a Haar measure, the orthogonality relations between coefficients of inequivalent irreducible representations, or the decomposition of the square-integrable functions on G into finite-dimensional invariant subspaces, and it says nothing about irreducible representations."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula At(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Instance(Formula cls) => Seq(OpenBracket, cls, CloseBracket, Comma, Esc);

    private static Formula DensityFormula()
    {
        Formula g = F.Id("G"), n = F.Id("n"), r = F.Id("r"), i = F.Id("i"), j = F.Id("j");
        Formula f = F.Id("f"), x = F.Id("g");
        Formula unitary = Call("unitaryGroup", Call("Fin", n), Complexes);
        Formula entry = new Formula.Subscript(At(r, x), Seq(i, Comma, j));
        Formula coefficient = Exists("n", Naturals,
            Exists("r", Call("ContinuousMonoidHom", g, unitary),
                Exists("i", Call("Fin", n),
                    Exists("j", Call("Fin", n),
                        ForAll("g", g, Equal(At(f, x), entry))))));
        Formula coefficients = Seq(OpenBrace,
            Rel(f, FormulaRelationOperator.MemberOf, Call("C", g, Complexes)),
            Sp, Mid, Sp, coefficient, CloseBrace);
        return Disp(ForAll("G", TypeStar, Seq(
            Instance(Call("Group", g)),
            Instance(Call("TopologicalSpace", g)),
            Instance(Call("IsTopologicalGroup", g)),
            Instance(Call("CompactSpace", g)),
            Call("Dense", Call("span", Complexes, coefficients)))));
    }
}
