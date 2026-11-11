using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalOcticSplitDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split determinant of the original octic window is irreducible over every characteristic-zero splitting field.",
        H("The labeled octic window"),
        Blocks(
            Paragraph(Text("Let alpha be an element of a field D with alpha to the eighth power equal to two. Let sigma_0 through sigma_7 be embeddings into a characteristic-zero field k. Fix a primitive eighth root zeta in k and preserve the labels sigma_i(alpha)=sigma_0(alpha) zeta^i. The four columns are the images of 1, alpha, alpha^3 and alpha^4 in that order. The polynomial is the determinant of the eight columns [B | diag(q) B], with rows labeled zero through seven. In the formulas, fourSets is the set of all four-element subsets of Fin 8, and RingHomFamily(Fin 8,D,k) means a family of eight unital ring homomorphisms from D to k. The exponent i is the representative zero through seven of its original label.")),
            Describe.Lean(DescribeId.Create("normalized-coefficient-count"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.coefficient_zero_count"),
                H("The exact normalized coefficient count"),
                StatementSource.FromAuthor(CountStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are seventy four-element label sets. The normalized integer coefficient function vanishes at eighteen of them. Its other values belong to the set consisting of plus or minus one, two and four."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("original-determinant-structure"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_structure"),
                H("Structure of the actual determinant"),
                StatementSource.FromAuthor(StructureStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This statement derives homogeneity of degree four, degree at most one in each variable and exactly eighteen zero squarefree quartic coefficients from the root relations themselves.")),
                    Paragraph(Text("Put s=zeta+zeta^3, so s squared equals minus two. If U is the matrix of the first four rows of B, the last four rows are R U, where the rows of R are (-1,-s,2,s), (-s,1,s,0), (0,-s,1,s) and (-s,2,s,-1). The square of det(U) is 128. Block elimination expresses the eight-by-eight determinant as 128 times the determinant whose entry (i,j) is R(i,j)(q_(4+i)-q_j). Expanding this four-by-four determinant gives precisely the normalized integer coefficients counted above. No row permutation changes the original labels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-determinant-irreducibility"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalOcticSplitDeterminant.original_split_determinant_irreducible"),
                H("Irreducibility with the original embeddings"),
                StatementSource.FromAuthor(IrreducibilityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Applying each embedding to alpha^8=2 identifies its row with the root matrix used in the structure theorem. The homogeneous multiaffine quartic obstruction applies because eighteen is less than twenty. Thus the actual determinant is irreducible over k. The statement quantifies every characteristic-zero field containing these embeddings and the primitive root, so it also applies after further field extension.")),
                    Paragraph(Text("The original field element, its four powers and all eight embedding labels remain explicit. This determinant statement does not assert a classification of rational windows with equal quotient support."))),
                DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open,
            Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Labels() => Call("Fin", D(8));
    private static Formula P() => Call("splitDeterminant",
        Call("originalWindowMatrix", F.Id("a"), F.Id("z")));
    private static Formula ZeroCount(Formula f) => Call("card", Seq(OpenBrace, F.Id("I"),
        InMacro, Sp, F.Id("fourSets"), Mid, Call("coeff", f, Call("squareExponent", F.Id("I"))), Eq, D(0), CloseBrace));
    private static Formula CountStatement() => Disp(Seq(Call("card", Seq(OpenBrace, F.Id("I"),
        InMacro, Sp, F.Id("fourSets"), Mid, Call("integerCoefficient", F.Id("I")), Eq, D(0), CloseBrace)), Eq, D(1,8)));
    private static Formula FieldAssumptions() => Seq(Call("Field", F.Id("k")), Land, Call("CharZero", F.Id("k")));
    private static Formula StructureStatement() => Disp(Seq(Forall, Sp, F.Id("k"), Comma, Sp,
        FieldAssumptions(), Implies, All("a", F.Id("k"), All("z", F.Id("k"), Seq(
            F.Id("a"), Caret, Grp(D(8)), Eq, D(2), Land, Call("IsPrimitiveRoot", F.Id("z"), D(8)),
            Implies, Call("IsHomogeneous", P(), D(4)), Land,
            Open, All("i", Labels(), Seq(Call("degreeOf", F.Id("i"), P()), Le, D(1))), Close,
            Land, ZeroCount(P()), Eq, D(1,8))))));
    private static Formula IrreducibilityStatement() => Disp(Seq(Forall, Sp, F.Id("k"), Comma, Sp,
        Forall, Sp, F.Id("D"), Comma, Sp, FieldAssumptions(), Land, Call("Field", F.Id("D")), Implies,
        All("alpha", F.Id("D"), All("sigma", Call("RingHomFamily", Labels(), F.Id("D"), F.Id("k")),
        All("z", F.Id("k"), Seq(F.Id("alpha"), Caret, Grp(D(8)), Eq, D(2), Land,
            Call("IsPrimitiveRoot", F.Id("z"), D(8)), Land,
            Open, All("i", Labels(), Seq(Call("sigma", F.Id("i"), F.Id("alpha")), Eq,
                Call("sigma", D(0), F.Id("alpha")), Cdot, Sp, F.Id("z"), Caret, Grp(F.Id("i")))), Close,
            Implies, Call("Irreducible", Call("splitDeterminant",
                Call("originalFieldWindowMatrix", F.Id("alpha"), F.Id("sigma"))))))))));
}
