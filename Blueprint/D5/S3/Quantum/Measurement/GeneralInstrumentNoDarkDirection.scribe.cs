using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class GeneralInstrumentNoDarkDirectionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/GeneralInstrumentNoDarkDirection.no_dark_direction_tfae";

    private static readonly Formula N = F.Id("N"), A = F.Id("a"), I = F.Id("i"), Eff = F.Id("F");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A general no-click instrument has no definite dark direction exactly when its limit effect vanishes, "
            + "exactly when the survival defect after d steps is positive definite, and exactly when "
            + "Tr(rho F) = 0 for every density matrix rho.",
        H("No Definite Dark Direction for General Instruments"),
        Blocks(Describe.Lean(
            DescribeId.Create("general-no-dark-direction"),
            DeclarationHandle.Create(Declaration),
            H("Four equivalent forms of the absence of dark directions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the "
                        + "d-dimensional space with the completeness relation, let S_N be the survival effects, "
                        + "D_d the stable dark layer and F the limit of S_N. The four conditions are: D_d is zero; "
                        + "F is zero; I - S_d is positive definite; Tr(rho F) = 0 for every density matrix rho.")),
                Paragraph(Text(
                    "Every vector of D_d satisfies S_N v = v from step d on, so F v = v; hence F = 0 forces D_d = 0. "
                        + "Conversely, if F is not zero, the Rayleigh quotient of F attains a largest value lambda > 0 "
                        + "on the unit sphere, so lambda I - F is positive semidefinite. On its kernel M, which "
                        + "contains the maximizer, the fixed-point equation gives <v, F v> = sum over a of "
                        + "<Q_a v, F Q_a v>, which is at most lambda times the sum of |Q_a v|^2, that is lambda "
                        + "(|v|^2 - sum of |L_i v|^2). Equality forces every L_i v to vanish and every Q_a v to lie "
                        + "in M, so M is a nonzero subspace annihilated by the click operators and invariant under "
                        + "the no-click operators, and it lies in D_d.")),
                Paragraph(Text(
                    "Since D_d is the kernel of the positive semidefinite operator I - S_d, it is zero exactly when "
                        + "I - S_d is positive definite. Testing F against the rank-one densities v v^* / |v|^2 "
                        + "shows that Tr(rho F) = 0 for all densities exactly when F = 0."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complete = Seq(
            Sum, Underscore, Grp(A, Sp, InMacro, Sp, Alpha), Sp, Sub("Q", A), Caret, Grp(Star), Sp, Sub("Q", A),
            Sp, Plus, Sp, Sum, Underscore, Grp(I, Sp, InMacro, Sp, Iota), Sp,
            Sub("L", I), Caret, Grp(Star), Sp, Sub("L", I), Sp, Eq, Sp, F.Id("I"));
        Formula limit = Seq(Sub("S", N), Sp, To, Sp, Eff);
        Formula density = Seq(
            Forall, Sp, F.Rho, Sp, Geq, Sp, D(0), Sp, F.Text, Grp(Sp, F.Id("with"), Sp),
            Operatorname, Grp(F.Id("Tr")), Sp, F.Rho, Sp, Eq, Sp, D(1), Comma, Sp,
            Operatorname, Grp(F.Id("Tr")), Open, F.Rho, Sp, Eff, Close, Sp, Eq, Sp, D(0));
        return Disp(Seq(
            Grp(complete, Sp, Land, Sp, limit), Sp, Rightarrow, RowBreak, Grp(),
            Sub("D", F.Id("d")), Sp, Eq, Sp, D(0), Sp, Iff, Sp, Eff, Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            F.Id("I"), Minus, Sub("S", F.Id("d")), Sp, Gt, Sp, D(0), Sp, Iff, RowBreak, Grp(),
            density, Dot));
    }

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
}
