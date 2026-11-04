using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class SingularHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Solenoid/SingularHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-degree ordinary singular homology group of the universal solenoid is zero, proved through genuine continuous lifts of all singular simplices.",
        H("Singular Homology of the Universal Solenoid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solenoid-normalized-source-lift"),
                DeclarationHandle.Create(Prefix + "exists_unique_normalized_lift"),
                H("Normalized real parameter on a simply connected source"),
                StatementSource.FromAuthor(LiftStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A be simply connected and locally path-connected, let f be a continuous map from A to the universal solenoid, "
                    + "and choose a basepoint a0. The circle covering supplies a continuous real lift of the visible projection of f minus f(a0), normalized to zero at a0. "
                    + "The remaining difference lies in the hidden kernel. Every modulus-m coordinate of that difference is m-torsion, hence lies in a finite discrete subset of the circle. "
                    + "Connectedness makes every such coordinate constant, and its value at a0 is zero. The real-flow injectivity theorem gives uniqueness. "
                    + "This result is used on the live proof path of the singular homology calculation below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solenoid-positive-singular-homology"),
                DeclarationHandle.Create(Prefix + "singular_homology_positive_is_zero"),
                H("Positive-degree integral singular homology vanishes"),
                StatementSource.FromAuthor(HomologyStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write B for the set of path components, equipped with a new discrete topology, and choose one solenoid point xb in each component. "
                        + "The map q from B times the real line sends (b,t) to realFlow(t) plus xb. The existing path-orbit classification and real-flow injectivity make q a continuous bijection. "
                        + "The proof does not identify the quotient topology on path components with this discrete topology.")),
                    Paragraph(Text(
                        "Apply normalized source lifting to every finite-dimensional standard simplex. Each singular simplex in the solenoid lifts to a continuous map into B times the real line. "
                        + "Injectivity of q makes the lift unique. The actual natural transformation obtained by applying TopCat.toSSet to q is therefore bijective in every degree and hence an isomorphism of simplicial sets; "
                        + "its face and degeneracy compatibility comes from the singular functor itself.")),
                    Paragraph(Text(
                        "On the resolution B times the real line, multiplying the real coordinate by 1-s gives a homotopy from the identity to the section-projection composite through B. "
                        + "Mathlib's homotopy invariance and positive-degree vanishing for totally disconnected spaces then prove the integral singular homology object is zero. "
                        + "The target is ordinary singular homology in positive degrees; the path-component contribution in degree zero is retained. "
                        + "Cech invariants require a separate calculation. The existing recurrence theorem proves that realFlow is not an embedding.")),
                    Paragraph(Text(
                        "This is a formal calculation using standard covering-space and singular-homology mathematics, with no claim of a new mathematical theorem. "
                        + "The library contribution is the proved bridge from the project's inverse-limit dynamical carrier to genuine singular simplices and categorical homology."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula LiftStatement() => Disp(F.Seq(
        Forall, Sp, F.Id("A"), Comma, Sp,
        Call("SimplyConnectedSpace", F.Id("A")), Comma, Sp,
        Call("LocallyPathConnectedSpace", F.Id("A")), Comma, Sp,
        Forall, Sp, F.Id("f"), Colon, Sp, Call("ContinuousMap", F.Id("A"), F.Id("Sigma")), Comma, Sp,
        Forall, Sp, F.Id("a0"), Colon, Sp, F.Id("A"), Comma, Sp,
        Exists, Bang, Sp, F.Id("r"), Colon, Sp, Call("ContinuousMap", F.Id("A"), F.Id("R")), Comma, Sp,
        Call("r", F.Id("a0")), Eq, D(0), Comma, Sp,
        Forall, Sp, F.Id("a"), Comma, Sp,
        Call("f", F.Id("a")), Eq,
        Call("realFlow", Call("r", F.Id("a"))), Plus, Call("f", F.Id("a0")), Dot));

    private static Formula HomologyStatement() => Disp(F.Seq(
        Forall, Sp, F.Id("n"), Colon, Sp, F.Id("N"), Comma, Sp,
        F.Id("n"), Neq, D(0), Sp, Implies, Sp,
        Call("singularHomology", F.Id("Sigma"), F.Id("Z"), F.Id("n")), Eq, D(0), Dot));
}
