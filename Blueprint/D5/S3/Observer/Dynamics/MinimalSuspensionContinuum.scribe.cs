using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class MinimalSuspensionContinuumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A minimal compact suspension with positive continuous roof is compact and connected.",
        H("Minimal Suspension Continuum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-positive-roof-suspension-is-a-continuum"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Dynamics/MinimalSuspensionContinuum."
                        + "minimal_suspension_compact_connected"),
                H("A minimal positive-roof suspension is a continuum"),
                StatementSource.FromAuthor(SuspensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The suspension is constructed from the compact normalized leaf domain. "
                            + "Its physical height at (x,u) is u times r(x), and the upper endpoint "
                            + "at x is identified with the lower endpoint at T(x). Strict "
                            + "positivity makes this physical endpoint relation a setoid.")),
                    Paragraph(Text(
                        "Each base point determines a connected interval fiber. Consecutive "
                            + "fibers along a forward T-orbit meet at the identified endpoint, so "
                            + "their union is connected. Minimality makes the orbit dense; the "
                            + "product and quotient density lemmas make the fiber union dense in "
                            + "the whole suspension, whose connected closure is therefore all.")),
                    Paragraph(Text(
                        "Compactness is inherited from the compact fundamental domain through the "
                            + "quotient. Repository and pinned-Mathlib searches found no packaged "
                            + "mapping-torus theorem; the proof directly applies the exact compact "
                            + "quotient, connected-chain, dense-product, quotient-density, and "
                            + "connected-closure results."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula SuspensionFormula()
    {
        Formula k = F.Id("K");
        Formula t = F.Id("T");
        Formula r = F.Id("r");
        Formula x = F.Id("x");
        Formula n = F.Id("n");
        Formula h = F.Id("h");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula iterate = Seq(t, Caret, n);
        Formula suspension = Apply(F.Id("Suspension"), t, r, h);

        return Disp(Seq(
            Forall, Sp, k, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Typeclass("MetricSpace", k), Comma, Sp,
            Typeclass("CompactSpace", k), Comma, Sp,
            Typeclass("Nonempty", k), Comma, Esc,
            t, Colon, Sp, Apply(Seq(Operatorname, Grp(F.Id("Homeomorph"))), k, k), Comma, Sp,
            r, Colon, Sp, k, Sp, To, Sp, reals, Comma, RowBreak,
            h, Colon, Sp, Open, Forall, Sp, x, Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(r, x), Close, Comma, RowBreak,
            Apply(Seq(Operatorname, Grp(F.Id("Continuous"))), r), Sp, Land, RowBreak,
            Open, Forall, Sp, x, Comma, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("DenseRange"))),
                Seq(Open, n, InMacro, Sp, naturals, Sp, Mapsto, Sp,
                    Apply(iterate, x), Close)), Close, Sp, Rightarrow, RowBreak,
            Apply(Seq(Operatorname, Grp(F.Id("IsCompact"))),
                Apply(Seq(Operatorname, Grp(F.Id("univ"))), suspension)), Sp, Land, RowBreak,
            Apply(Seq(Operatorname, Grp(F.Id("IsConnected"))),
                Apply(Seq(Operatorname, Grp(F.Id("univ"))), suspension)), Dot));
    }
}
