using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class GlobalAffineGcdBehaviorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/PrimePowers/GlobalAffineGcdBehavior.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual local quotient codes classify all legal finite words and have a common positive source.",
        H("Global affine behavior and joint local realization"),
        Blocks(Describe.Lean(
            DescribeId.Create("global-encoding-complete"),
            DeclarationHandle.Create(Prefix + "global_encoding_complete"),
            H("Exact behavior of the original positive operation library"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix H at least two and a finite list A of positive integer addends. "
                    + "Put d = libraryGcd(H,A), with d = H when A is empty. Each prime "
                    + "p dividing H has h = H.factorization(p) and e = d.factorization(p). "
                    + "The function globalEncoding(H,A,x) is the dependent tuple of the actual "
                    + "localEncoding(p,h,e,x modulo p^h) on these prime axes. Its codomain "
                    + "GlobalCode(H,A) is the product of the typed LocalCode(p,h,e) spaces.")),
                Paragraph(Text(
                    "Two positive sources have equal global codes exactly when every same "
                    + "legal finite word produces equal gcds with H, and exactly when every "
                    + "same word produces equal quotients H/gcd. Legal words contain positive "
                    + "multiplications and indexed additions from A, include the empty word, "
                    + "and have no fixed length bound. A multiplier congruent to zero is "
                    + "permitted: the positive multiplier H represents that residue.")),
                Paragraph(Text(
                    "If two codes differ, one prime axis and one positive multiplier followed "
                    + "by a finite list of original additions give different gcd exponents "
                    + "on that axis for the same two sources. Writing d = p^e t, the cofactor "
                    + "t is coprime to p and is a unit modulo p^(h-e). A local signed "
                    + "translation p^e delta is therefore represented by one nonnegative "
                    + "global coefficient b in d b. When e = h, that translation vanishes "
                    + "on the axis and b = 0 suffices. The original-library affine realization "
                    + "supplies the finite list of additions. Other prime axes may change; "
                    + "a different exponent on the chosen axis already distinguishes the gcds.")),
                Paragraph(Text(
                    "Conversely, a mixed word has a positive affine slope and a translation "
                    + "divisible by d. Equal local codes preserve every such depth. The depth "
                    + "on each prime axis is exactly its exponent in the output gcd, so the "
                    + "global gcds agree. Since both gcds divide the same positive H, their "
                    + "quotients agree exactly when the gcds agree.")),
                Paragraph(Text(
                    "Every tuple of typed local labels is attained by one positive source. "
                    + "First choose the integer representative of each label supplied by the "
                    + "local completeness theorem. The Chinese remainder equivalence for "
                    + "the actual prime-power factors of H gives one residue z modulo H. "
                    + "The positive integer z.val + H represents it simultaneously on every "
                    + "axis, including when the residue is zero."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
                items.Add(Seq(Comma, Sp));
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Positive() => Seq(Nat(), Underscore, Grp(Gt, D(0)));
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));

    private static Formula Statement()
    {
        Formula h = F.Id("H"), library = F.Id("A"), x = F.Id("x"), y = F.Id("y");
        Formula w = F.Id("w"), p = F.Id("p"), a = F.Id("a"), ws = F.Id("ws");
        Formula c = F.Id("c"), words = Call("List", Call("Operation", library));
        Formula code(Formula z) => Call("globalEncoding", h, library, z);
        Formula output(Formula word, Formula z) => Call("runWord", library, word, z);
        Formula gcd(Formula word, Formula z) => Call("gcd", output(word, z), h);
        Formula behavior(bool quotient) => All(x, Positive(), All(y, Positive(), Iff(
            Equal(code(x), code(y)), All(w, words, Equal(
                quotient ? Call("div", h, gcd(w, x)) : gcd(w, x),
                quotient ? Call("div", h, gcd(w, y)) : gcd(w, y))))));
        Formula special = Call("multiplyThenAdd", a, ws);
        Formula separator = All(x, Positive(), All(y, Positive(), Seq(
            Par(Seq(code(x), Sp, Neq, Sp, code(y))), Sp, Rightarrow, Sp,
            Some(p, Call("primeFactors", h), Some(a, Positive(),
                Some(ws, Call("List", Call("Fin", Call("length", library))), Seq(
                    Call("factorization", gcd(special, x), p), Sp, Neq, Sp,
                    Call("factorization", gcd(special, y), p))))))));
        Formula onto = All(c, Call("GlobalCode", h, library),
            Some(x, Positive(), Equal(code(x), c)));
        Formula result = Par(Seq(Par(behavior(false)), Sp, Land, Sp,
            Par(behavior(true)), Sp, Land, Sp, Par(separator), Sp, Land, Sp, Par(onto)));
        return Disp(All(h, Nat(), All(library, Call("List", Positive()), Seq(
            Par(Seq(D(2), Sp, Le, Sp, h)), Sp, Rightarrow, Sp, result))));
    }
}
