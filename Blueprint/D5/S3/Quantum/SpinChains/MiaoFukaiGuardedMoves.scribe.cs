using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class MiaoFukaiGuardedMovesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/MiaoFukaiGuardedMoves.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/SpinModels/miaofukai2026novel");

    private static readonly Formula L = F.Id("L");
    private static readonly Formula J = F.Id("j");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Fin = Call("Fin", L);
    private static readonly Formula Config = Call("Config", L);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The guarded matrix entries determine charge conservation and two-sided annihilation.",
        H("Guarded moves and projector charge on the periodic ladder"),
        Blocks(
            Paragraph(Text("Labelled words of length L use the empty rung and the symmetric and antisymmetric one-boson rungs of Eq. (69). Config is the subtype in which each cyclic consecutive pair has an empty rung. All scalar actions use the complex numbers. A matrix entry has the output word as its row and the input word as its column.")),
            Paragraph(Text("The diagonal entry of P at site j is the indicator of a minus at j plus the squared difference of the two flanking empty indicators. The unextended charge adds these indicators over the cycle as in Eq. (45). The centre move A interchanges empty and plus at j with both flanks empty. The flank move F interchanges both occupied signs about an empty centre. Both moves use unit matrix entries. Their sum is the unextended generator S of Eq. (70). The controlled generator T is C times S, where C is the square of the difference of the two flanking projectors.")),
            Paragraph(Text("Jammed means that at every site with projector value zero, both flanking projector values equal one. The diagonal control then kills the row of a jammed word at that site. A site of projector value one has no move. The guarded involutions complement the flanking projector bits for each move, so the same condition kills the column as well. A nonzero controlled move must exchange the two flanking bits and preserve every other projector bit.")),
            Theorem("successor", "Periodic successor index", "next_val", Length(All(J, Fin,
                Eq(Value(Call("next", J)), Call("if", Lt(NextIndex(), L), NextIndex(), D(0))))),
                "The successor of the last rung is the first rung."),
            Theorem("predecessor", "Periodic predecessor index", "prev_val", Length(All(J, Fin,
                Eq(Value(Call("prev", J)), Call("if", Eq(Value(J), D(0)), Seq(L, Minus, D(1)), Seq(Value(J), Minus, D(1)))))),
                "The predecessor of the first rung is the last rung."),
            Theorem("local-kills", "Two-sided annihilation by the local generator", "jammed_kills",
                Local(All(X, Config, Imp(Call("Jammed", X), Kills(AtSite("T"))))),
                "The delta vector is the basis ket and the same coordinates give its dual row."),
            Theorem("local-charge", "Charge across a nonzero entry", "charge_of_nonzero_entry",
                Local(All(X, Config, All(Y, Config, Imp(Ne(Call("entry", AtSite("T"), Y, X), D(0)),
                    Eq(Call("charge", Y), Call("charge", X)))))),
                "The two complemented bits have sum one on each endpoint of a controlled move."),
            Theorem("charge-eigenvalue", "Projector charge of a basis ket", "charge_eigenvalue",
                Length(All(X, Config, Eq(Call("mulVec", Call("NP", L), Ket()),
                    Call("smul", Call("ofNat", Call("charge", X)), Ket())))),
                "The diagonal matrix of summed charge acts by the complex cast of that charge."),
            Theorem("controlled-square", "Square of the controlled generator", "controlled_square",
                Local(Eq(Square(AtSite("T")), Mul(AtSite("C"), Square(AtSite("S"))))),
                "The control is idempotent and constant across each transition of the unextended move."),
            Theorem("ladder-densities", "The two contributions to each ladder density", "ladder_density_parts",
                Local(And(Eq(AtSite("T"), Add(Centre("A"), Flanks("F"))),
                    Eq(Square(AtSite("T")), Add(Centre("DA"), Flanks("DF"))))),
                "Ue is the squared difference of the two empty projectors at distance two. Um is the squared difference of the minus projectors on the adjacent sites. DA is the projector onto a centre that is not minus with two empty flanks. DF projects onto two occupied flanks. These give the two five-rung pieces in Eq. (71)."),
            Theorem("ladder-kills", "Each controlled ladder contribution annihilates a jammed word", "ladder_parts_kill",
                Length(Imp(Le(D(5), L), All(X, Config, Imp(Call("Jammed", X), All(J, Fin, LadderKills()))))),
                "The centre and flank contributions have disjoint support for both the first and second powers, giving separate row and column vanishing."))));

    private static DocumentBlock Theorem(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("miao-fukai-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var symbol = Seq(Operatorname, Grp(F.Id(name)));
        return arguments.Length == 0 ? symbol : new Formula.Apply(symbol, [.. arguments]);
    }
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, variable, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula AtSite(string name) => Call(name, J);
    private static Formula Value(Formula x) => Call("val", x);
    private static Formula NextIndex() => Add(Value(J), D(1));
    private static Formula Length(Formula body) => All(L, Nat, body);
    private static Formula Local(Formula body) => Length(Imp(Le(D(5), L), All(J, Fin, body)));
    private static Formula Ket() => Call("ket", X);
    private static Formula Centre(string name) => Mul(AtSite("Ue"), AtSite(name));
    private static Formula Flanks(string name) => Mul(AtSite("Um"), AtSite(name));
    private static Formula LadderKills() =>
        And(Kills(Centre("A")), And(Kills(Flanks("F")), And(Kills(Centre("DA")), Kills(Flanks("DF")))));
    private static Formula Kills(Formula matrix) =>
        And(Eq(Call("mulVec", matrix, Ket()), D(0)), Eq(Call("vecMul", Ket(), matrix), D(0)));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Square(Formula x) => new Formula.Power(x, D(2));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
}
