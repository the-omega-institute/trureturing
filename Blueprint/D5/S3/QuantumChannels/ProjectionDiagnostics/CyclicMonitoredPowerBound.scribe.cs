using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class CyclicMonitoredPowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cyclic monitored operator has a strictly contracting power.",
        H("Cyclic monitored power contraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-monitored-power-contraction"),
            DeclarationHandle.Create("D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredPowerBound.cyclic_power_contraction"),
            H("A strict power bound derived from actual cyclicity"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every finite dimensional complex Hilbert space, every unitary U and every "
                + "unit vector v, C is the actual span of U^n v, and T_C is the restriction of "
                + "(I-P_v)U. No stability or independent cyclicity hypothesis is imposed. "
                + "The actual cyclic future-kernel theorem proves zero dark space. "
                + "Orthogonal coordinates carry T_C and the actual click restriction to a "
                + "conservative singleton instrument. FiniteDetectionSurvivalLimit.dark_block_contraction "
                + "then supplies the strict gap; its estimate is reused directly. "
                + "The chosen N is dim C and q is the norm of T_C^N. "
                + "The contraction holds on the actual cyclic space. It does not assert the infinite "
                + "weighted return identity or identify dim C with occupied spectral cardinality. "
                + "The complete monitored-return endpoint is classical, as in Grunbaum, Velazquez, "
                + "Werner and Werner, arXiv:1202.3903v3, Theorem 2."))),
            DescribeRole.Theorem))));

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Statement()
    {
        Formula e = F.Id("E"), u = F.Id("U"), v = F.Id("v"), n = F.Id("N"), q = F.Id("q");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula estimate = And(Seq(D(0), Le, Sp, q), And(Seq(q, Lt, D(1)),
            Seq(new Formula.Norm(Seq(Call("cyclicStep", u, v), Caret, n)), Le, Sp, q)));
        Formula result = Bind(FormulaQuantifier.Exists, "N", Seq(Mathbb, Grp(F.Id("N"))),
            And(Seq(D(1), Le, Sp, n),
                Bind(FormulaQuantifier.Exists, "q", Seq(Mathbb, Grp(F.Id("R"))), estimate)));
        Formula law = new Formula.Logic(Seq(new Formula.Norm(v), Eq, D(1)),
            FormulaLogicOperator.Implies, result);
        return Disp(Bind(FormulaQuantifier.ForAll, "E", F.Id("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
            OpenBracket, Call("InnerProductSpace", complex, e), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", complex, e), CloseBracket, Comma, Quad,
            Bind(FormulaQuantifier.ForAll, "U", Call("LinearIsometryEquiv", complex, e, e),
                Bind(FormulaQuantifier.ForAll, "v", e, law)))));
    }
}
