using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockChargedIrreducibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual charged polynomial Heisenberg modes have only zero and full invariant subspaces.",
        H("Charged Polynomial Fock Irreducibility"),
        Blocks(
            Paragraph(Text("Let F=C[X_0,X_1,...]. For every complex charge r, "
                + "alpha^(r)_0 is r times the identity, alpha^(r)_(j+1) is "
                + "(j+1) times partial differentiation in X_j, and "
                + "alpha^(r)_(-j-1) is multiplication by X_j, for every natural j. "
                + "The nonzero modes are the existing concrete polynomial Fock modes. "
                + "Write chargedMode(r,n,p)=alpha^(r)_n p.")),
            Describe.Lean(
                DescribeId.Create("charged-polynomial-fock-modes-irreducible"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/PolynomialFockChargedIrreducibility.charged_modes_irreducible"),
                H("Every invariant complex subspace is zero or full"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("S"), InMacro,
                    Call("Submodule", Seq(Mathbb, Grp(F.Id("C"))), F.Id("F")), Comma, Esc,
                    Open, Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("F"), Comma, Sp,
                    F.Id("p"), InMacro, Sp, F.Id("S"), Rightarrow,
                    Call("chargedMode", F.Id("r"), F.Id("n"), F.Id("p")),
                    InMacro, Sp, F.Id("S"), Close, Rightarrow, Sp,
                    F.Id("S"), Eq, OpenBrace, D(0), CloseBrace,
                    Lor, Sp, F.Id("S"), Eq, F.Id("F")))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997freeboson")),
                Blocks(
                    Paragraph(Text("There is no restriction on the charge or the dimension "
                        + "of the subspace. Invariance is required for every integer mode "
                        + "and every polynomial in the subspace. It is not an assumed "
                        + "irreducible representation or an assumed vertex-algebra module.")),
                    Paragraph(Text("In a nonzero invariant subspace, select a nonzero "
                        + "polynomial of least total degree. Positive-mode invariance and "
                        + "the invertibility of j+1 give closure under every partial derivative. "
                        + "A nonzero partial derivative would have smaller total degree, "
                        + "so all partial derivatives of the selected polynomial vanish. "
                        + "Characteristic zero makes it a nonzero constant. Scaling gives "
                        + "the unit; negative modes then create every monomial, and "
                        + "linearity gives the whole polynomial algebra.")),
                    Paragraph(Text("Matsuo-Nagatomo, Section 2.2, printed pages 20-21, "
                        + "states the charged polynomial representation and its irreducibility. "
                        + "The identification is x_(j+1)=X_j. The charge r differs from "
                        + "a conformal background-charge parameter. This result concerns "
                        + "Heisenberg modes; it does not establish Virasoro irreducibility, "
                        + "charged all-state module Jacobi, intertwiners or fusion, "
                        + "a Monster realization, string theory or AdS/CFT geometry."))),
                DescribeRole.Theorem))));
}
