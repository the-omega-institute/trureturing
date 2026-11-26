using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.ConcentratableEntanglement;

internal sealed class TwoProductConcentratableEntanglementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/ConcentratableEntanglement/TwoProductConcentratableEntanglement.";
    private static readonly LibraryNoteRef Gce =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual generalized concentratable entanglement of a coherent two-product state is monotone and submodular for every real order above one.",
        H("Subsystem inequalities for coherent two-product states"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-two-product-gce"),
                DeclarationHandle.Create(Owner + "actual_two_product_gce"),
                H("Monotonicity and submodularity of literal two-product GCE"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(Gce),
                Blocks(
                    Paragraph(Text("A datum Ψ is a nonzero coherent sum of two finite tensor products of local complex unit vectors, "
                        + "with arbitrary complex coefficients and possibly different finite local dimensions. Its density matrix is normalized by the squared norm. "
                        + "C(K, Ψ, S) subtracts the mean of the real power traces of the actual reductions over subsets of S from one, then divides by K − 1.")),
                    Paragraph(Text("The physical moment supplier relates every reduction to two spectral values and supplies the phase-dependent mass bound. "
                        + "For positive local overlap magnitudes the logarithms of their squared magnitudes make the cut parameter additive. "
                        + "A convex scalar spectral profile then gives supermodularity of the powerset-averaged moments. "
                        + "The continuous scalar boundary argument also covers zero overlaps. "
                        + "Complement symmetry equates the averages before and after the final site is added, so submodularity forces earlier increments to be nonnegative.")),
                    Paragraph(Text("The stated domain is literal two-product sums, not arbitrary pure states, arbitrary states of cut rank at most two, or a secant-closure theorem."))),
                DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula P(Formula f) => Seq(Open, f, Close);

    private static Formula Statement()
    {
        var k = F.Id("K");
        var x = F.Id("Q");
        var a = F.Id("A");
        var b = F.Id("B");
        var domain = Call("Subsets", Call("Sites", x));
        Formula C(Formula s) => Call("C", k, x, s);
        var overlap = new Formula.Relation(
            new Formula.Binary(C(Call("Intersection", a, b)), FormulaBinaryOperator.Add, C(Call("Union", a, b))),
            FormulaRelationOperator.LessThanOrEqual,
            new Formula.Binary(C(a), FormulaBinaryOperator.Add, C(b)));
        var both = new Formula.Logic(P(Call("Monotone", Call("C", k, x))), FormulaLogicOperator.And,
            P(All("A", domain, All("B", domain, overlap))));
        var law = new Formula.Logic(P(new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, k)),
            FormulaLogicOperator.Implies, P(both));
        return Disp(All("K", Seq(Mathbb, Grp(F.Id("R"))), All("Q", F.Id("NonzeroTwoProductData"), law)));
    }
}
