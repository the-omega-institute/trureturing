using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class IdentityJordanFullGroupTraceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Representation/IdentityJordanFullGroupTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The identity and rational Jordan actions have trace two on every integer element.",
        H("Identity and Jordan Full Group Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("jordan-integer-power"),
                DeclarationHandle.Create(DeclarationPrefix + "rho_unipotent_integer_power"),
                H("Every integer Jordan power has a linear upper-right entry"),
                StatementSource.FromAuthor(IntegerPowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The modular-group power formula is mapped entrywise from integers to "
                            + "rationals. Its generator is the existing rational Jordan unit, "
                            + "so the cyclic action at m has upper-right entry m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-group-trace-two"),
                DeclarationHandle.Create(DeclarationPrefix + "full_group_trace_two"),
                H("Both traces equal two on the full integer group"),
                StatementSource.FromAuthor(TraceTwoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The integer power formula leaves both diagonal entries equal to one. "
                            + "The identity action has the same diagonal, so both traces are "
                            + "two for every integer group element."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-exponent-audit"),
                DeclarationHandle.Create(DeclarationPrefix + "zero_exponent_audit"),
                H("Exponent zero collapses both actions to identity"),
                StatementSource.FromAuthor(ZeroAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At m equal to zero, the off-diagonal entry vanishes. The Jordan action "
                            + "is the identity matrix and agrees with the constant identity "
                            + "representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-exponent-audit"),
                DeclarationHandle.Create(DeclarationPrefix + "negative_exponent_audit"),
                H("Negative one gives the inverse and preserves trace two"),
                StatementSource.FromAuthor(NegativeAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At m equal to negative one, the upper-right entry is negative one. "
                            + "This is the explicit inverse Jordan matrix, whose diagonal still "
                            + "has trace two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-trace-not-isomorphic"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "same_full_trace_but_not_isomorphic"),
                H("Full trace equality does not imply representation isomorphism"),
                StatementSource.FromAuthor(TraceContrastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The traces agree at every integer element, while the existing minimal "
                            + "polynomial argument proves the two generator matrices are not "
                            + "conjugate. Full character data therefore misses this extension."))),
                DescribeRole.Theorem))));

    private static Formula IntegerPowerFormula()
    {
        Formula m = F.Id("m");
        Formula action = Call("act", F.Id("rhoUnipotent"), m);
        Formula matrix = Call("matrix2", D(1), m, D(0), D(1));
        return Disp(Seq(Forall, Sp, m, Comma, Sp, Equal(action, matrix)));
    }

    private static Formula TraceTwoFormula()
    {
        Formula m = F.Id("m");
        Formula unipotentTrace = Equal(
            Call("trace", Call("act", F.Id("rhoUnipotent"), m)),
            D(2));
        Formula identityTrace = Equal(
            Call("trace", Call("act", F.Id("rhoZero"), m)),
            D(2));
        return Disp(Seq(
            Forall, Sp, m, Comma, Sp,
            unipotentTrace, Sp, Land, Sp, identityTrace));
    }

    private static Formula ZeroAuditFormula()
    {
        Formula zeroAction = Call("act", F.Id("rhoUnipotent"), D(0));
        Formula identity = Call("identityMatrix", D(2));
        Formula trivialAction = Call("act", F.Id("rhoZero"), D(0));
        return Disp(Seq(
            Equal(zeroAction, identity), Sp, Land, Sp,
            Equal(zeroAction, trivialAction)));
    }

    private static Formula NegativeAuditFormula()
    {
        Formula negativeOne = Seq(Minus, D(1));
        Formula action = Call("act", F.Id("rhoUnipotent"), negativeOne);
        Formula matrix = Call("matrix2", D(1), negativeOne, D(0), D(1));
        Formula trace = Equal(Call("trace", action), D(2));
        return Disp(Seq(Equal(action, matrix), Sp, Land, Sp, trace));
    }

    private static Formula TraceContrastFormula()
    {
        Formula m = F.Id("m");
        Formula unipotentTrace = Call("trace", Call("act", F.Id("rhoUnipotent"), m));
        Formula identityTrace = Call("trace", Call("act", F.Id("rhoZero"), m));
        Formula sameTrace = Seq(
            Open, Forall, Sp, m, Comma, Sp,
            Equal(unipotentTrace, identityTrace), Close);
        Formula generator = F.Id("cycleGenerator");
        Formula notConjugate = Seq(
            Neg, Sp,
            Call(
                "IsConj",
                Call("act", F.Id("rhoZero"), generator),
                Call("act", F.Id("rhoUnipotent"), generator)));
        return Disp(Seq(sameTrace, Sp, Land, Sp, notConjugate));
    }
}
