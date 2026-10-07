using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class LogConvolutionMassExpansionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef ScalarSource =
        LibraryNoteRef.Create("D5/L/ArithSums/tao2026logpartialsums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute coefficient mass controls a signed logarithmic Dirichlet convolution at every real cutoff.",
        H("Logarithmic Convolution from Absolute Coefficient Mass"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-convolution-mass-expansion"),
                DeclarationHandle.Create("D5/S3/Arith/LogConvolutionMassExpansion.logarithmic_convolution_mass_expansion"),
                H("Two absolute moments and an exact mass error bound"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(ScalarSource),
                Blocks(
                    Paragraph(Text("Let g be a real ArithmeticFunction and assume only that the sum of "
                        + "|g(n)| over all natural indices is finite. The carrier gives g(0)=0. "
                        + "The quotients at index zero use Lean's real division convention and equal zero; "
                        + "the logarithmic term there is also zero. Coefficients may have either sign. "
                        + "Define the mass, two signed weighted sums, and the summatory convolution by:"),
                        Math(DefinitionsFormula())),
                    Paragraph(Text("Both displayed weighted series converge absolutely. For every real y>=1, "
                        + "the theorem gives the displayed two-term expansion with error at most "
                        + "M_g(1+log y). The cutoff is the natural floor of y. No inverse identity, "
                        + "positive coefficient condition, stronger logarithmic moment hypothesis, "
                        + "or assumed remainder estimate occurs in the theorem.")),
                    Paragraph(Text("The proof bounds both absolute weights by |g(n)|. The existing "
                        + "summatory Dirichlet convolution identity rewrites the cutoff sum as a finite "
                        + "sum of g(n) log(floor(y/n)!). For 1<=x<=y, the classical integral bounds "
                        + "for partial logarithmic sums give |log(floor x)!-(x log x-x)|<=1+log y. "
                        + "For 0<x<1, the floor is zero and x(1-log x)<=1; x=0 is handled directly. "
                        + "Coefficients outside the cutoff multiply a zero factorial logarithm. "
                        + "The weighted main terms and the absolutely summable error can therefore "
                        + "be combined by the existing infinite-sum APIs. The triangle inequality "
                        + "bounds the total signed error by the entire absolute mass.")),
                    Paragraph(Text("Three private scalar suppliers are minimal ports of Terence Tao's "
                        + "Mathlib/Analysis/SpecialFunctions/Log/Sum.lean at immutable revision "
                        + "0826a5e4ff8877949060d03ce8955545bfb2b47f, under Apache-2.0. "
                        + "The pinned Mathlib lacks that file. Its factorial identity and upper/lower "
                        + "real-cutoff logarithmic sum bounds supply the scalar estimate; they do not "
                        + "state this generic convolution theorem. The live convolution, moment and "
                        + "infinite-sum composition is repository work using those classical suppliers. "
                        + "No borrowed-proof originality or separate open-problem resolution is claimed. "
                        + "The ports should be retired when equivalent declarations enter the project pin.")),
                    Paragraph(Text("The generic result alone does not identify constants of the actual "
                        + "golden Binet inverse or the derivative of its literal Dirichlet series. "
                        + "Those require a separate application with the actual absolute-tail gap "
                        + "and a proved series/derivative bridge."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var g = F.Id("g"); var n = F.Id("n"); var y = F.Id("y");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula abs(Formula x) => new Formula.Absolute(x);
        Formula weight = new Formula.Fraction(Call("g", n), n);
        Formula logWeight = new Formula.Fraction(Seq(Call("g", n), Call("log", n)), n);
        Formula mass = new Formula.Subscript(F.Id("M"), g);
        Formula first = new Formula.Subscript(F.Id("U"), g);
        Formula second = new Formula.Subscript(F.Id("V"), g);
        Formula summable(Formula body) => Call("Summable", Seq(n, Mapsto, Sp, body));
        Formula error = abs(Seq(new Formula.Subscript(F.Id("K"), g), Open, y, Close,
            Minus, first, y, Call("log", y), Plus,
            Open, first, Plus, second, Close, y));
        Formula bound = Seq(mass, Open, D(1), Plus, Call("log", y), Close);
        return Disp(Seq(Forall, Sp, g, InMacro, Sp, Call("ArithmeticFunction", real), Comma, Sp,
            summable(abs(Call("g", n))), Rightarrow, Sp,
            summable(abs(weight)), Land, Sp, summable(abs(logWeight)), Land, Sp,
            Forall, Sp, y, InMacro, Sp, real, Comma, Sp, D(1), Le, Sp, y,
            Rightarrow, Sp, error, Le, Sp, bound));
    }

    private static Formula DefinitionsFormula()
    {
        var g = F.Id("g"); var n = F.Id("n"); var y = F.Id("y");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula sum(Formula body) => Seq(new Formula.Subscript(Sum, Seq(n, InMacro, Sp, nat)), body);
        Formula sub(string name) => new Formula.Subscript(F.Id(name), g);
        Formula convolution = Seq(Call("DirichletConvolution", g, Log), Open, n, Close);
        Formula cutoff = Seq(D(0), Lt, Sp, n, Le, Sp, Lfloor, Sp, y, Rfloor);
        return Disp(Seq(sub("M"), Eq, Sp, sum(new Formula.Absolute(Call("g", n))), Comma, Sp,
            sub("U"), Eq, Sp, sum(new Formula.Fraction(Call("g", n), n)), Comma, Sp,
            sub("V"), Eq, Sp,
            sum(new Formula.Fraction(Seq(Call("g", n), Call("log", n)), n)), Comma, Sp,
            sub("K"), Open, y, Close, Eq, Sp, new Formula.Subscript(Sum, cutoff), convolution));
    }
}
