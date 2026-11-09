using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class NorthSouthOrbitClockDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma, Sp);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula HeightFormula() => Seq(
        All("M", Id("CompactMetricSpace")), All("f", Call("Homeomorphism", Id("M"))),
        All("N", Id("M")), All("S", Id("M")),
        Call("Pointwise", Id("f"), Id("N"), Id("S")), Sp, Rightarrow, Sp,
        Call("Nonempty", Call("StrictHeight", Id("f"), Id("N"), Id("S"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal pointwise north-south dynamics supplies a continuous strict height through locally finite integer orbit sums.",
        H("A Proper Integer Orbit Clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pointwise-strict-height"),
                DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/NorthSouthOrbitClock.exists_strictHeight"),
                H("The height is constructed from pointwise dynamics"),
                StatementSource.FromAuthor(HeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The assumptions are precisely Pointwise f N S on an arbitrary compact metric "
                        + "space. The resulting continuous real height takes values in [-1,1], takes "
                        + "-1 exactly at N and 1 exactly at S, and strictly increases under f at every "
                        + "other point. No height, clock, flow, rate, stability or uniformity is assumed.")),
                    Paragraph(Text(
                        "The raw distance difference d(p,N)-d(p,S) has the same zero cut as the "
                        + "normalized distance function because d(p,N)+d(p,S)>0. The compact set "
                        + "u(p)≤0≤u(f(p)) meets each punctured orbit. A continuous nonnegative bump "
                        + "is positive on that cut and vanishes near both poles. Compact uniform "
                        + "attraction bounds its nonzero integer translates on every compact subset "
                        + "of the punctured space, hence locally. Thus B(p)=sum b(f^i(p)) and "
                        + "A(p)=sum i b(f^i(p)) are actual finite sums with B>0.")),
                    Paragraph(Text(
                        "Finite reindexing gives B(fp)=B(p), A(fp)=A(p)-B(p), and t(fp)=t(p)+1 "
                        + "for t=-A/B. Stability at the poles forces all positive-weight indices "
                        + "to escape in the appropriate direction, so t tends to positive infinity "
                        + "at S and negative infinity at N. The compression t/(1+abs(t)) extends "
                        + "continuously with the prescribed endpoint values. If the punctured space "
                        + "is empty, its clock obligations are vacuous and the same extension covers "
                        + "the two-point space.")),
                    Paragraph(Text(
                        "This follows the supplied proof SHA-256 "
                        + "9d2c8af332171841b0de2122a8a6d18d3f094b8ee563ff2b50646332144306bc "
                        + "and formal route SHA-256 "
                        + "1a51a2083580f57293ae2e0f032afb5257d891328f247d26b97b81b483360a97. "
                        + "The reusable inference added here is the derived proper clock and its "
                        + "endpoint extension; the result alone is not the full selector theorem."))),
                DescribeRole.Theorem))));
}
