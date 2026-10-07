using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciActualCommonImagePlateauDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Fn(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            Seq(Operatorname, Grp(V(name)), Open, Join(args, Seq(Comma, Sp)), Close);
    private static Formula Join(Formula[] items, Formula separator)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var index = 0; index < items.Length; index++)
        {
            if (index > 0) result.Add(separator);
            result.Add(items[index]);
        }
        return Seq([.. result]);
    }
    private static Formula At(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Local(string name, Formula value, Formula body) =>
        Seq(Operatorname, Grp(V("let")), Sp, V(name), Eq, Sp, value, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Open, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body, Close);
    private static Formula PolynomialRing => Seq(V("R"), OpenBracket, V("X"), CloseBracket);
    private static Formula FinR => Call("Fin", V("r"));
    private static Formula ObservationRange => Call("range", V("O"));
    private static Formula Image(Formula n) => Sub(V("I"), n);

    private static Formula Statement()
    {
        var n = V("n");
        var i = V("i");
        var ai = At(V("a"), i);
        var phiAi = At(V("Phi"), ai);
        var hypotheses = Seq(
            D(2), Leq, Sp, V("k"), Sp, Land, Sp,
            D(2), Leq, Sp, V("d"), Sp, Land, Sp,
            D(1), Leq, Sp, V("r"), Sp, Land, Sp,
            Call("Injective", V("a")), Sp, Land, Sp,
            Open, All("i", FinR, Seq(D(2), Leq, Sp, ai)), Close);
        var phi = Lambda("b", Nat, Seq(Pow(V("X"), V("b")), Minus,
            Sum, Underscore, Grp(V("j"), InMacro, Sp, Call("range", V("b"))),
            Pow(V("X"), V("j"))));
        var quotient = Seq(Prod, Underscore, Grp(i, Colon, Sp, FinR),
            Call("AdjoinRoot", phiAi));
        var q = Lambda("P", PolynomialRing, Seq(Open,
            At(Sub(V("mk"), phiAi), V("P")), Close, Underscore, Grp(i, Colon, Sp, FinR)));
        var observation = Lambda("P", PolynomialRing, Seq(Open,
            V("P"), Sp, Operatorname, Grp(V("modByMonic")), Sp, phiAi,
            Close, Underscore, Grp(i, Colon, Sp, FinR)));
        var wordPolynomial = Lambda("n", Nat, Lambda("w", Fn(Call("Fin", n), Call("Bool")),
            Seq(Sum, Underscore, Grp(i, Colon, Sp, Call("Fin", n)),
                Call("bit", At(V("w"), i)), Pow(V("X"), Call("val", i)))));
        var images = Lambda("n", Nat, Seq(OpenBrace,
            V("y"), Colon, Sp, Fn(FinR, PolynomialRing), Sp, Mid, Sp,
            Exists, Sp, V("w"), Colon, Sp, Fn(Call("Fin", n), Call("Bool")), Comma, Sp,
            Call("DBonacciAdmissible", V("k"), n, V("w")), Sp, Land, Sp,
            At(V("O"), Call("Pw", n, V("w"))), Eq, Sp, V("y"), CloseBrace));
        var fullLengths = Seq(OpenBrace, n, InMacro, Sp, Nat, Sp, Mid, Sp,
            Image(n), Eq, Sp, ObservationRange, CloseBrace);
        var plateau = All("n", Nat, Seq(Open,
            Image(n), Eq, Sp, Image(Seq(n, Plus, D(2))), Sp, Implies, Sp,
            Image(n), Eq, Sp, ObservationRange, Close));
        var least = Seq(Exists, Sp, V("N"), InMacro, Sp, Nat, Comma, Sp,
            Call("IsLeast", fullLengths, V("N")), Sp, Land, Sp,
            V("N"), Leq, Sp, D(2), V("M"), Minus, D(3), Sp, Land, Sp,
            Open, All("n", Nat, Seq(Open, Image(n), Eq, Sp, ObservationRange,
                Sp, Leftrightarrow, Sp, V("N"), Leq, Sp, n, Close)), Close);
        var conclusion = Seq(Open, plateau, Close, Sp, Land, Sp, Open, least, Close);
        var locals = Local("R", Call("ZMod", V("d")),
            Local("Phi", phi, Local("Q", quotient, Local("q",
                Seq(q, Colon, Sp, Call("RingHom", PolynomialRing, V("Q"))),
            Local("H", Call("range", V("q")), Local("O", observation,
            Local("Pw", wordPolynomial, Local("I", images,
            Local("M", Call("card", V("H")), conclusion)))))))));
        return All("k", Nat, All("d", Nat, All("r", Nat,
            All("a", Fn(FinR, Nat), Seq(Open, hypotheses, Close, Sp, Implies, Sp, locals)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every two-step plateau of the exact-length legal common image is already the full "
            + "polynomial image. Its first saturation length is at most twice the common-image "
            + "cardinality minus three, including composite coefficient moduli.",
        H("Two-step growth of actual common polynomial images"),
        Blocks(
            Paragraph(Text(
                "Fix k and d at least two and a nonempty finite injective family of probe "
                    + "orders a_i at least two. The coefficient ring is ZMod d. Each Phi_b "
                    + "is X^b minus the sum of X^j for zero at most j below b. The map q "
                    + "sends one polynomial to its classes in all the AdjoinRoot quotients, "
                    + "and H is q.range with its induced ring structure. The map O returns "
                    + "the monic remainder representatives in all coordinates. Thus range O "
                    + "is a carrier equivalent to H, and M is Nat.card H.")),
            Paragraph(Text(
                "A word w has type Fin n to Bool, with position zero at the constant term. "
                    + "The function bit sends false to zero and true to one in ZMod d. Pw(n,w) "
                    + "is its polynomial. I_n is the raw tuple image of accepted words of "
                    + "exact length n, using the original DBonacciAdmissible k scanner. One "
                    + "word and one polynomial supply every probe. Every zero occupies a "
                    + "position, and n ranges over all natural numbers, including zero. "
                    + "IsLeast(S,N) means N belongs to S and is at most every member of S.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-actual-common-image-plateau-and-budget"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciActualCommonImagePlateau."
                        + "kbonacci_actual_common_image_plateau_and_budget"),
                H("No proper two-step plateau and the first exact full-image length"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite polynomial quotient by the product of all Phi_(a_i) maps "
                            + "onto H. Its root is a unit, so multiplication by x, the image "
                            + "of X, is injective on finite H. Projection onto any probe gives "
                            + "M at least d^(a_i), hence M at least four. Monic remainder "
                            + "representatives inject into raw polynomial tuples; their "
                            + "multiplication is quotient multiplication followed by remainder.")),
                    Paragraph(Text(
                        "Appending a high-side false bit preserves value and acceptance. "
                            + "Prepending a low-side false bit multiplies the value by x. "
                            + "Appending the literal high-side suffix false,true adds "
                            + "x^(n+1), and its delimiter preserves acceptance even at k=2 "
                            + "and n=0. These operations give the required inclusions into "
                            + "length n+1 or n+2 without changing k.")),
                    Paragraph(Text(
                        "At a two-step plateau S, the finite injective images xS and "
                            + "S+x^(n+1) equal S. Iteration makes each multiplication by x^j "
                            + "surjective on S. Pulling back the translation by x^(n+1) and "
                            + "cancelling this unit gives closure under addition of one. "
                            + "Pulling back by x^j then gives closure under addition of x^j. "
                            + "Repeating this addition by a coefficient's natural representative "
                            + "and summing monomials gives every polynomial translation. "
                            + "The all-false word supplies zero, so S is all H. All these "
                            + "pullbacks act on algebraic images.")),
                    Paragraph(Text(
                        "Every proper image therefore gains at least one element in two "
                            + "positions. The length-one image is exactly the distinct pair "
                            + "zero,one. Induction gives card I_(2j+1) at least min(M,j+2). "
                            + "Taking j=M-2 gives full image at the single common exact length "
                            + "2M-3. The least full-image length N exists and is at most that "
                            + "bound. Counted high-side zero padding preserves saturation at "
                            + "every later length; minimality gives the converse.")),
                    Paragraph(Text(
                        "The conclusion concerns the accepted remainder image and bit "
                            + "length. It asserts no sharp threshold, terminal-tail or phase "
                            + "constraint, runtime bound, reconstruction of an unknown word, "
                            + "or replacement of the scanner's rejection output."))),
                DescribeRole.Theorem))));
}
