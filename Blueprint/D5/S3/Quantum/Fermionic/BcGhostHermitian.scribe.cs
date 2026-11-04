using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostHermitianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/BcGhostHermitian.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed Hermitian and literal c0-relative pairings on the original finite-support bc occupation Fock space.",
        H("Original bc Hermitian and relative ghost metric"),
        Blocks(
            Paragraph(Text("Here actualFock denotes exactly CountableOccupationFock.Fock, the Finsupp space (Finset Nat) →₀ Complex, and FinsetNat denotes Finset Nat. Relative is the subtype of actualFock in relativeSpace = ker(b 0). The notation (x : actualFock) is the subtype coercion. The support is the finite Finsupp support, star is complex conjugation, eps is the original sorted-word sign, and relativeEps(S) = eps(S) * phase(3, partner(S)). The relative pairing is exactly Hrel(x,y) = Hg((x : actualFock), c(0,(y : actualFock))).")),
            Paragraph(Text("The four-slot escape audit of all 96 remaining public theorem targets in this module is unfinished. The current compiled report has empty inventory, records and registered arrays, and the source-owned Reg mirror is absent. The exact full telescopes, existing enrolled-template contract and missing source reconstruction, bridge, readout, variation, sensitivity and observational dependence evidence are tracked in https://github.com/the-omega-institute/trureturing/issues/25743. This issue supplies the permitted missing-evidence disclosure; it is not a registration certificate or a judge-failure claim.")),
            Theorem("hg-signed-coefficient", "Hg_signed_coefficient", "Finite-support signed coefficient expansion",
                SignedCoefficientFormula(false),
                "The ambient pairing is the actual finite Finsupp sum over the support of x, with the derived epsilon sign and involutive partner."),
            Theorem("hg-hermitian", "Hg_hermitian", "Ordinary Hermitian symmetry",
                Quant2("x", "y", "actualFock", Equal(Call("Hg", F.Id("x"), F.Id("y")), Call("star", Call("Hg", F.Id("y"), F.Id("x"))))),
                "Hermitian symmetry is proved from the vacuum base, creator and annihilator adjoints, and the finite occupation induction."),
            Theorem("hg-radicals", "Hg_left_radical", "Zero left radical",
                RadicalFormula(false, true),
                "The involutive partner row and nonzero derived epsilon force every coefficient of a left-radical vector to vanish."),
            Theorem("hg-radicals-right", "Hg_right_radical", "Zero right radical",
                RadicalFormula(false, false),
                "The same finite-support coefficient argument proves the right radical is zero."),
            Theorem("hg-literal-dagger", "Hg_literal_dagger", "Literal reversed dagger word",
                Quant("S", "FinsetNat", Quant("y", "actualFock", Equal(Call("Hg", Call("ket", F.Id("S")), F.Id("y")), Call("rho", Call("daggerWord", Seq(F.Id("S"), Dot, Call("sort", Leq)), F.Id("y")))))),
                "The row is represented by the literal reverse-ordered dagger word on the original occupation ket."),
            Theorem("hg-b-adjoint", "Hg_b", "All-integer b adjoint",
                QuantMode("m", "x", "y", "b", "actualFock", Equal(Call("Hg", Call("b", F.Id("m"), F.Id("x")), F.Id("y")), Call("Hg", F.Id("x"), Call("b", Call("neg", F.Id("m")), F.Id("y"))))),
                "Both b cuts and every exceptional and bulk integer mode are covered by one derived theorem."),
            Theorem("hg-c-adjoint", "Hg_c", "All-integer c adjoint",
                QuantMode("n", "x", "y", "c", "actualFock", Equal(Call("Hg", Call("c", F.Id("n"), F.Id("x")), F.Id("y")), Call("Hg", F.Id("x"), Call("c", Call("neg", F.Id("n")), F.Id("y"))))),
                "The original c vacuum cut and all integer branches use the same native signed pairing."),
            Theorem("ghost-charge", "charge_partner", "Partner charge sum",
                Quant("S", "FinsetNat", Equal(Call("add", Call("charge", F.Id("S")), Call("charge", Call("partner", F.Id("S")))), D(3))),
                "The exact original signed charge is contragredient under the derived partner involution."),
            Theorem("hg-charge-selection", "Hg_charge_selection", "Ambient charge selection",
                AmbientChargeSelectionFormula(),
                "Selection is derived from the coefficient support and the exact partner charge identity."),
            Theorem("relative-hermitian", "Hrel_hermitian", "Literal c0-relative Hermitian symmetry",
                Quant2("x", "y", "Relative", Equal(Call("Hrel", F.Id("x"), F.Id("y")), Call("star", Call("Hrel", F.Id("y"), F.Id("x"))))),
                "The relative form is Hg(x,c0 y) on the actual kernel of b0; its symmetry follows from the derived c0 adjoint."),
            Theorem("relative-signed-coefficient", "Hrel_signed_coefficient", "Relative finite-support signed expansion",
                SignedCoefficientFormula(true),
                "The c0 insertion produces the exact relative partner and lowerCount sign on every arbitrary finite support."),
            Theorem("relative-radicals", "Hrel_left_radical", "Zero relative left radical",
                RadicalFormula(true, true),
                "The relative pairing has no left radical on the actual ker(b0) carrier."),
            Theorem("relative-radicals-right", "Hrel_right_radical", "Zero relative right radical",
                RadicalFormula(true, false),
                "The relative partner involution and nonzero relative epsilon give the right radical proof."),
            Theorem("relative-charge", "charge_relativePartner", "Relative partner charge sum",
                Quant("S", "FinsetNat", Implies(Call("notMem", D(3), F.Id("S")), Equal(Call("add", Call("charge", F.Id("S")), Call("charge", Call("relativePartner", F.Id("S")))), D(2)))),
                "Removing the forced c0 site changes the exact charge selection from three to two."),
            Theorem("relative-charge-selection", "Hrel_charge_selection", "Relative charge selection",
                RelativeChargeSelectionFormula(),
                "The relative selection rule is obtained by the actual c0 charge shift and the ambient theorem."))));

    private static DocumentBlock Theorem(string id, string declaration, string title, Formula statement, string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula Quant(string name, string type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, F.Id(type), Comma, Sp, body, Close);

    private static Formula Quant2(string first, string second, string type, Formula body) =>
        Quant(first, type, Quant(second, type, body));

    private static Formula QuantMode(string mode, string first, string second, string op, string type, Formula body) =>
        Quant(mode, "Int", Quant(first, type, Quant(second, type, body)));

    private static Formula AmbientChargeSelectionFormula()
    {
        Formula g = F.Id("g");
        Formula h = F.Id("h");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula premises = And(
            Call("Homogeneous", g, x),
            And(Call("Homogeneous", h, y),
                NotEqual(Call("add", g, h), D(3))));
        Formula body = Implies(premises, Equal(Call("Hg", x, y), D(0)));
        return Quant("g", "Int", Quant("h", "Int",
            Quant("x", "actualFock", Quant("y", "actualFock", body))));
    }

    private static Formula RelativeChargeSelectionFormula()
    {
        Formula g = F.Id("g");
        Formula h = F.Id("h");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula premises = And(
            Call("Homogeneous", g, Coerce("x")),
            And(Call("Homogeneous", h, Coerce("y")),
                NotEqual(Call("add", g, h), D(2))));
        Formula body = Implies(premises, Equal(Call("Hrel", x, y), D(0)));
        return Quant("g", "Int", Quant("h", "Int",
            Quant("x", "Relative", Quant("y", "Relative", body))));
    }

    private static Formula Coerce(string name) =>
        Seq(Open, F.Id(name), Colon, Sp, F.Id("actualFock"), Close);

    private static Formula SignedCoefficientFormula(bool relative)
    {
        Formula x = relative ? Coerce("x") : F.Id("x");
        Formula y = relative ? Coerce("y") : F.Id("y");
        Formula s = F.Id("S");
        Formula coefficientX = Seq(x, Open, s, Close);
        Formula coefficientY = Seq(y, Open,
            Call(relative ? "relativePartner" : "partner", s), Close);
        Formula summand = new Formula.Binary(
            new Formula.Binary(Call("star", coefficientX), FormulaBinaryOperator.Multiply,
                Call(relative ? "relativeEps" : "eps", s)),
            FormulaBinaryOperator.Multiply, coefficientY);
        Formula finiteSum = Seq(Sum, Underscore,
            Grp(s, InMacro, Call("support", x)), Sp, summand);
        return Quant2("x", "y", relative ? "Relative" : "actualFock",
            Equal(Call(relative ? "Hrel" : "Hg", F.Id("x"), F.Id("y")), finiteSum));
    }

    private static Formula RadicalFormula(bool relative, bool left)
    {
        string type = relative ? "Relative" : "actualFock";
        string outer = left ? "x" : "y";
        string inner = left ? "y" : "x";
        Formula premise = Quant(inner, type,
            Equal(Call(relative ? "Hrel" : "Hg", F.Id("x"), F.Id("y")), D(0)));
        return Quant(outer, type, Implies(premise, Equal(F.Id(outer), D(0))));
    }

    private static Formula Implies(Formula left, Formula right) =>
        Seq(left, Sp, F.Implies, Sp, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
