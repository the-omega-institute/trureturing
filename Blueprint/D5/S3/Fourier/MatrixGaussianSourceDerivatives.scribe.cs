using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class MatrixGaussianSourceDerivativesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite mixed complex coordinate derivatives of a positive matrix lattice Gaussian are the actual lattice monomial moments.",
        H("MatrixGaussianSourceDerivatives"), Blocks(
            Describe.Lean(DescribeId.Create("matrixgaussiansourcederivatives-sourcepartial"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianSourceDerivatives.sourcePartial"),
                H("Ordered finite source differentiation"),
                StatementSource.FromAuthor(Disp(Equal(Call("sourcePartial",Call("cons",V("i"),V("is")),V("f"),V("z")),
                    Call("derivAtZero",Seq(V("t"),Mapsto,Call("sourcePartial",V("is"),V("f"),Add(V("z"),Multiply(V("t"),Call("basisVector",V("i")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The empty list returns f(z). Prepending coordinate i differentiates the remaining function along z+t e_i at t=0. Coordinates may repeat. An empty rank admits only the empty list."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("matrixgaussiansourcederivatives-sourcepartial-tsum"),
                DeclarationHandle.Create("D5/S3/Fourier/MatrixGaussianSourceDerivatives.sourcePartial_tsum"),
                H("Every finite mixed source derivative commutes with the lattice sum"),
                StatementSource.FromAuthor(TheoremFormula()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite rank, positive definite real Gram matrix A, complex b with positive real part, finite ordered list of coordinates and arbitrary complex source z, the mixed derivative is the sum of the product of the indicated integer coordinates times the original sourceful Gaussian. The proof bounds the coordinate product by the corresponding power of the lattice sup norm, applies the genuine polynomial Gaussian majorant on a bounded complex coordinate disk, and uses Mathlib.hasSum_deriv_of_summable_norm. A single list induction covers every finite order; no source summability or extraction assumption is imposed.")),
                    Paragraph(Text("This is source differentiation at fixed Gaussian parameter b. It supplies finite source extraction, and makes no assertion of the still separate original mod-two theta S law or any fullK, Jacobi, VOA/CFT, BRST/string or AdS/CFT conclusion."))),DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C => Seq(Mathbb,Grp(V("C")));
    private static Formula All(string s, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula TheoremFormula()
    {
        var cv = new Formula.TypeArrow(Call("Fin",V("r")),C);
        var iv = new Formula.TypeArrow(Call("Fin",V("r")),V("Z"));
        var g = Call("latticeSourceMap",V("A"),V("b"),V("a"),V("z"));
        var theta = Seq(V("z"),Mapsto,Call("tsum",Seq(V("a"),Colon,iv,Mapsto,g)));
        var rhs = Call("tsum",Seq(V("a"),Colon,iv,Mapsto,
            Multiply(Call("listProduct",V("is"),Seq(V("i"),Mapsto,Call("castComplex",Call("a",V("i"))))),g)));
        var eq = Equal(Call("sourcePartial",V("is"),theta,V("z")),rhs);
        return Disp(All("r",V("N"),All("A",Call("RealMatrix",V("r")),
            Imp(Call("PosDef",V("A")),All("b",C,
                Imp(new Formula.Relation(D(0),FormulaRelationOperator.LessThan,Call("re",V("b"))),
                    All("is",Call("List",Call("Fin",V("r"))),All("z",cv,eq))))))));
    }
}
