using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class CriticalDampingFlatnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/Symmetry/CriticalDampingFlatness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite centered damping defect vanishes exactly when every damping rate is critical.",
        H("Critical Damping Flatness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-centered-damping-defect"),
                DeclarationHandle.Create(Prefix + "criticalDampingDefect"),
                H("Finite centered damping defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The defect is constructed by summing the nonnegative centered hyperbolic-cosine "
                        + "contribution of every member of the finite multiplicity-indexed zero window."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vanishing-damping-defect-characterizes-critical-rates"),
                DeclarationHandle.Create(Prefix + "critical_damping_flatness_criterion"),
                H("Vanishing damping defect characterizes critical rates"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite carrier records the zero window with multiplicity, and realPart "
                            + "records its damping rates. The displayed defect is the trace-cosh sum "
                            + "after centering those rates at one half.")),
                    Paragraph(Text(
                        "Every summand is nonnegative. A zero total therefore makes each summand zero, "
                            + "and Mathlib's strict hyperbolic-cosine criterion together with the "
                            + "nonzero scale forces every centered rate to vanish."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula zero = F.Id("Zero");
        Formula realPart = F.Id("realPart");
        Formula tau = F.Tau;
        Formula rho = F.Rho;
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrierType = Seq(Operatorname, Grp(F.Id("Type")));
        Formula rateType = Seq(zero, Sp, Mapsto, Sp, real);
        Formula critical = Fraction(D(1), D(2));
        Formula allCritical = Seq(
            Forall, Sp, rho, Sp, InMacro, Sp, zero, Comma, Sp,
            Call("realPart", rho), Sp, Eq, Sp, critical);
        Formula defectZero = Seq(
            Call("criticalDampingDefect", realPart, tau), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, zero, Colon, Sp, carrierType, Comma, Sp,
            realPart, Colon, Sp, rateType, Comma, Sp,
            tau, Sp, InMacro, Sp, real, Comma, RowBreak, Grp(),
            Call("Fintype", zero), Sp, Land, Sp,
            tau, Sp, Neq, Sp, D(0), Sp, Rightarrow, RowBreak, Grp(),
            Open, allCritical, Close, Sp, Leftrightarrow, Sp,
            defectZero, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
