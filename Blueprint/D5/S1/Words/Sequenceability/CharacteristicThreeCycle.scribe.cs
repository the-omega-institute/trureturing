using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class CharacteristicThreeCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var ztype = Product(U, Fthree);
        var charge = Call("ite", Seq(F.Id("a"), Cdot, Call("fst", F.Id("z")), Eq, D(1)), D(1), D(0));
        var update = Pair(Seq(F.Id("a"), Cdot, Call("fst", F.Id("z"))),
            Seq(Minus, Call("snd", F.Id("z")), Plus, charge));
        var stepFormula = Scope(false, All("a", U, All("z", ztype,
            Eqn(Call("step", F.Id("a"), F.Id("z")), update))));
        var vertexFormula = Scope(false, All("z", ztype, Eqn(Call("vertex", F.Id("z")),
            Pair(Call("fst", F.Id("z")), Call("snd", F.Id("z"))))));
        var difference = Pair(Seq(Open, F.Id("a"), Minus, D(1), Close, Cdot, Call("fst", F.Id("z"))),
            Seq(Call("snd", F.Id("z")), Plus, charge));
        var labelFormula = Scope(false, All("a", U, Seq(F.Id("a"), Neq, Sp, D(1), Rightarrow, Sp,
            All("z", ztype, Eqn(Call("label", F.Id("a"), F.Id("z")), difference)))));
        var orbit = All("i", Call("Fin", M), Eqn(Call("e", F.Id("i")),
            Call("iterate", Call("step", F.Id("a")), Call("val", F.Id("i")), Pair(D(1), D(0)))));
        var full = Eqn(Call("iterate", Call("step", F.Id("a")), M, Pair(D(1), D(0))), Pair(D(1), D(0)));
        var labels = Call("Bijective", Seq(F.Id("i"), Mapsto, Sp,
            Call("label", F.Id("a"), Call("e", F.Id("i")))));
        var identity = All("z", ztype,
            Eqn(Seq(Call("vertex", Call("step", F.Id("a"), F.Id("z"))), Minus, Call("vertex", F.Id("z"))),
                Call("vertex", Call("label", F.Id("a"), F.Id("z")))));
        var cycle = Ex("e", Call("Equiv", Call("Fin", M), ztype),
            Seq(Open, orbit, Close, Land, Sp, full, Land, Sp, labels, Land, Sp, identity));
        var existence = Ex("a", U, Seq(F.Id("a"), Neq, Sp, D(1), Land, Sp,
            Eqn(Call("orderOf", F.Id("a")), F.Id("L")), Land, Sp, D(2), Le, Sp, F.Id("L"), Land, Sp,
            Call("Even", F.Id("L")), Land, Sp, cycle));
        var theorem = Scope(true, Let("L", Seq(Call("card", F.Id("K")), Minus, D(1)), existence));
        return DocumentDefinition.Create(ScribeNode.Create(
            "One finite-field orbit inventories its vertices and directed differences exactly.",
            H("Characteristic-three finite-field cycle"), Blocks(
                Paragraph(Text("Write U for the units of K and F for ZMod 3. The function ite is "
                    + "one when its condition holds and zero otherwise. Unit coordinates in additive "
                    + "expressions are coerced to K. The map iterate(f,n,z) is the actual n-fold iterate.")),
                Node("step", "step", "The phase and row update", stepFormula,
                    "Advance the multiplicative phase, reflect the row, and add one exactly on wrap.",
                    DescribeRole.Definition),
                Node("vertex", "vertex", "The additive vertex", vertexFormula,
                    "The vertex map coerces the unit coordinate to the field and preserves the row.",
                    DescribeRole.Definition),
                Node("label", "label", "The nonzero directed difference", labelFormula,
                    "A proof of a!=1 is an argument of the Lean definition and makes a-1 a unit. "
                    + "In characteristic three the row difference -2*t+q equals t+q.", DescribeRole.Definition),
                Node("cycle-inventory", "exists_cycle_inventory", "One complete orbit and its exact labels", theorem,
                    "Here M=3*L. The field and every finite characteristic-three extension remain in scope. "
                    + "Finite-field unit cyclicity supplies a of exact order L. Odd field cardinality "
                    + "makes L even and at least two, hence a-1 is nonzero. The powers below L "
                    + "biject onto the units. For i<L, the actual i-step orbit from (1,n) is "
                    + "(a^i,(-1)^i*n). One lap sends (1,n) to (1,n+1). Repeated laps construct "
                    + "the orbit equivalence e and three laps return to (1,0). Every directed label "
                    + "is successor minus current vertex, including every bridge and the closing edge. "
                    + "Multiplication by a-1 permutes the units and each row map t to t+q is a "
                    + "translation, proving the second bijection. Internal labels are "
                    + "((a-1)*a^i,-2*(-1)^i*n); bridge labels are ((a-1)*a^(L-1),2*n+1). "
                    + "Their row slopes are nonzero in F. The bridge n=-1 closes the cycle. "
                    + "L=2 and a=-1 are included by this same proof."))));
    }

    private static DocumentBlock.Describe Node(string id, string decl, string title, Formula formula,
        string text, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S1/Words/Sequenceability/CharacteristicThreeCycle." + decl),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
    private static Formula Op(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] xs) =>
        Seq(Op(s), Open, Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x }).ToArray()), Close);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
    private static Formula Product(Formula x, Formula y) => Seq(x, Times, Sp, y);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula All(string x, Formula ty, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, ty, Close, Comma, body);
    private static Formula Ex(string x, Formula ty, Formula body) =>
        Seq(Exists, Sp, Open, F.Id(x), Colon, ty, Close, Comma, body);
    private static Formula Let(string x, Formula value, Formula body) =>
        Seq(Op("let"), Sp, F.Id(x), Eq, value, Semi, body);
    private static Formula Scope(bool finite, Formula body) => All("K", Op("Type"),
        Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket,
            finite ? Seq(OpenBracket, Call("Fintype", F.Id("K")), CloseBracket,
                OpenBracket, Call("CharP", F.Id("K"), D(3)), CloseBracket) : Seq(), body));
    private static Formula Fthree => Call("ZMod", D(3));
    private static Formula U => Seq(F.Id("K"), Caret, Grp(Times));
    private static Formula M => Seq(D(3), Cdot, Sp, F.Id("L"));
}
