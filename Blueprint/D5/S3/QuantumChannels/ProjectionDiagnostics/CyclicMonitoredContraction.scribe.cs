using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class CyclicMonitoredContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cyclic monitored restriction has no nonzero all-future hidden vector.",
        H("Cyclic monitored observability"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-monitored-future-kernel"),
            DeclarationHandle.Create("D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredContraction.cyclic_future_kernel_eq_bot"),
            H("The actual cyclic restriction has zero future kernel"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every finite dimensional complex Hilbert space, every unitary U, and every "
                + "vector v, C is the span of the actual forward orbit U^n v. The operator T_C "
                + "is the restriction of (I-P_v)U and B_C is the restriction of P_v U. "
                + "Both preserve C. The theorem includes v=0 and requires no recurrence premise. "
                + "Orthogonal observability duality identifies the ambient hidden space; maximal "
                + "unobservability gives its invariance under the monitored step. On its intersection "
                + "with C the monitored step equals U. Finite dimensional injectivity supplies "
                + "surjectivity of this restricted U, hence inverse invariance. Every hidden cyclic "
                + "vector is then orthogonal to every U^n v and must vanish. "
                + "This observability conclusion supplies the zero dark space needed for cyclic "
                + "power contraction. A strict power norm bound and the infinite weighted return identity "
                + "are not asserted here. The recurrence and expected-return result is classical: "
                + "Grunbaum, Velazquez, Werner and Werner, arXiv:1202.3903v3, Theorem 2."))),
            DescribeRole.Theorem))));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Statement()
    {
        Formula e = F.Id("E"), u = F.Id("U"), v = F.Id("v"), x = F.Id("x"), n = F.Id("n");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula step = Call("cyclicStep", u, v);
        Formula clicked = Call("cyclicClick", u, v, Seq(Open, step, Caret, n, Close, Sp, x));
        Formula law = new Formula.Logic(
            All("n", Seq(Mathbb, Grp(F.Id("N"))), Seq(clicked, Eq, D(0))),
            FormulaLogicOperator.Implies, Seq(x, Eq, D(0)));
        return Disp(All("E", F.Id("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
            OpenBracket, Call("InnerProductSpace", complex, e), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", complex, e), CloseBracket, Comma, Quad,
            All("U", Call("LinearIsometryEquiv", complex, e, e),
                All("v", e, All("x", Call("cyclicSpace", u, v), law))))));
    }
}
