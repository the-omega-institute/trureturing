using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Dsl = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class HoneycombFirstTouchDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Synchronous first-touch dynamics and strict horizons in clipped honeycomb domains.",
        H("First touch in clipped honeycomb domains"),
        Blocks(
            Paragraph(Text("On the retained finite set, A(0,0) is born at tick zero. At positive "
                + "ticks, a newly born vertex sends to each retained neighbor. An untouched "
                + "vertex permanently records the tick and multiplicity of its first "
                + "nonempty set of proposals. Multiplicity one is birth. Higher multiplicity "
                + "blocks the vertex permanently.")),
            Paragraph(Text("The honeycomb step bound gives the earliest possible time "
                + "2(x+y)+p at color p and coordinates (x,y). At that time A births "
                + "satisfy Pascal's recurrence modulo two. A B vertex reads its single "
                + "earliest A predecessor. Lucas parity gives exactly the condition "
                + "that the nonnegative coordinates have no common set bit.")),
            Paragraph(Text("At dyadic P dividing m, compare heights m and N with 0 < m < N "
                + "and a common strict cut g < K, where g = 2x + y + p and 1 ≤ K ≤ 2m. "
                + "A crossing edge can leave the smaller domain only at the diagonal "
                + "A wall x+y=m. At 0 < y < P, the two parent coordinates have complementary "
                + "low bits and both parents send at tick 2m. At y ≥ P, the earliest-touch "
                + "bound alone excludes birth before 2x+p+2P. The horizon changes by at "
                + "most one along edges. Strong induction on time gives identical "
                + "first-touch data below each shared vertex's horizon and excludes "
                + "earlier exterior births.")),
            Paragraph(Text("For a retained vertex v of the smaller domain, a tick t strictly "
                + "below the horizon, and positive multiplicity μ, the two touch predicates satisfy "),
                Math(new Formula.Logic(Touch("m"), FormulaLogicOperator.Iff, Touch("N"))),
                Text(". Both runs use the seed A(0,0). At an exterior vertex in the larger "
                    + "domain, no birth occurs at any tick strictly below its horizon.")))));

    private static Formula Touch(string height) =>
        Call("Touch", Dsl.Id(height), Dsl.Id("K"), Dsl.Id("t"), Dsl.Id("v"), Mu);
}
