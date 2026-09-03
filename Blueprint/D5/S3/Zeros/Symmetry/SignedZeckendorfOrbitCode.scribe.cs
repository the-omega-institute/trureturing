using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class SignedZeckendorfOrbitCodeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/Symmetry/SignedZeckendorfOrbitCode."
            + "klein_actions_two_sign_bits";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three zero symmetries act on a signed W code by flipping its two sign coordinates.",
        H("Signed Zeckendorf Orbit Code"),
        Blocks(Describe.Lean(
            DescribeId.Create("klein-actions-on-two-sign-bits"),
            DeclarationHandle.Create(Declaration),
            H("Klein actions are the two independent sign flips"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public code is constructed from the centered real coordinate, the "
                        + "height, their golden-scale W encodings, and the multiplicity W word. "
                        + "Conjugation, conjugate reflection, and reflection induce the three "
                        + "displayed sign transformations while preserving every unsigned word.")),
                Paragraph(Text(
                    "The orbit-code list is equal to the explicitly listed sign-state list. "
                        + "When both centered coordinates are nonzero, the sign values are "
                        + "nonzero and each differs from its negative, so the four entries are "
                        + "pairwise distinct."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Conventions/WDigits")),
        ]));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(entries[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ListOf(params Formula[] entries)
    {
        var items = new List<Formula> { OpenBracket };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(entries[index]);
        }

        items.Add(CloseBracket);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula n = F.Id("N");
        Formula multiplicity = F.Id("multiplicity");
        Formula rho = F.Id("rho");
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula unsignedThread = F.Id("unsignedThread");
        Formula code = F.Id("code");
        Formula states = F.Id("states");
        Formula orbitCodes = F.Id("orbitCodes");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula codeCarrier = Seq(
            F.Id("SignType"), Sp, Times, Sp, F.Id("WDigitString"), Sp, Times, Sp,
            F.Id("SignType"), Sp, Times, Sp, F.Id("WDigitString"), Sp, Times, Sp,
            F.Id("WDigitString"));
        Formula rhoValue = Seq(
            half, Sp, Plus, Sp, delta, Sp, Plus, Sp,
            Call("ComplexI"), Sp, Times, Sp, gamma);
        Formula unsignedValue = Call(
            "wEncoding",
            new Formula.Floor(new Formula.Binary(
                new Formula.Power(Varphi, Grp(n)),
                FormulaBinaryOperator.Multiply,
                new Formula.Norm(x))));
        Formula centered(Formula value) =>
            new Formula.Binary(Call("re", value), FormulaBinaryOperator.Subtract, half);
        Formula unsigned(Formula value) =>
            new Formula.Apply(unsignedThread, [value]);
        Formula sign(Formula value) => Call("sign", value);
        Formula codeValue(Formula value) => new Formula.Apply(code, [value]);
        Formula wordMultiplicity = Call("wEncoding", multiplicity);
        Formula codeDefinition = Tuple(
            sign(centered(z)), unsigned(centered(z)), sign(Call("im", z)),
            unsigned(Call("im", z)), wordMultiplicity);
        Formula positiveState = Tuple(
            sign(delta), unsigned(delta), sign(gamma), unsigned(gamma), wordMultiplicity);
        Formula conjugateState = Tuple(
            sign(delta), unsigned(delta), new Formula.Negate(sign(gamma)),
            unsigned(gamma), wordMultiplicity);
        Formula mirrorState = Tuple(
            new Formula.Negate(sign(delta)), unsigned(delta), sign(gamma),
            unsigned(gamma), wordMultiplicity);
        Formula reflectionState = Tuple(
            new Formula.Negate(sign(delta)), unsigned(delta),
            new Formula.Negate(sign(gamma)), unsigned(gamma), wordMultiplicity);
        Formula conjugateRho = Call("conj", rho);
        Formula mirrorRho = new Formula.Binary(
            D(1), FormulaBinaryOperator.Subtract, conjugateRho);
        Formula reflectionRho = new Formula.Binary(
            D(1), FormulaBinaryOperator.Subtract, rho);
        Formula statesValue = ListOf(
            positiveState, conjugateState, mirrorState, reflectionState);
        Formula orbitCodesValue = ListOf(
            codeValue(rho), codeValue(conjugateRho), codeValue(mirrorRho),
            codeValue(reflectionRho));
        Formula genericClause = Implies(
            NotEqual(delta, D(0)),
            Implies(NotEqual(gamma, D(0)), Call("Nodup", orbitCodes)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, delta, Comma, Sp, gamma, Colon, Sp, real, Comma, Sp,
                n, Comma, Sp, multiplicity, Colon, Sp, naturals, Comma),
            Seq(
                Grp(), F.Id("let"), Sp, rho, Colon, Sp, complex, Sp, Eq, Sp,
                rhoValue, Semi),
            Seq(
                Grp(), F.Id("let"), Sp, unsignedThread, Colon, Sp,
                new Formula.TypeArrow(real, F.Id("WDigitString")), Sp, Eq, Sp,
                Lambda(x, unsignedValue), Semi),
            Seq(
                Grp(), F.Id("let"), Sp, code, Colon, Sp,
                new Formula.TypeArrow(complex, Grp(codeCarrier)), Sp, Eq, Sp,
                Lambda(z, codeDefinition), Semi),
            Seq(
                Grp(), F.Id("let"), Sp, states, Colon, Sp,
                Call("List", Grp(codeCarrier)), Sp, Eq, Sp, statesValue, Semi),
            Seq(
                Grp(), F.Id("let"), Sp, orbitCodes, Colon, Sp,
                Call("List", Grp(codeCarrier)), Sp, Eq, Sp, orbitCodesValue, Semi),
            Seq(
                Grp(), Equal(codeValue(conjugateRho), conjugateState), Sp, Land),
            Seq(
                Grp(), Equal(codeValue(mirrorRho), mirrorState), Sp, Land),
            Seq(
                Grp(), Equal(codeValue(reflectionRho), reflectionState), Sp, Land),
            Seq(
                Grp(), Equal(orbitCodes, states), Sp, Land),
            Seq(Grp(), genericClause, Dot),
        ]));
    }
}
