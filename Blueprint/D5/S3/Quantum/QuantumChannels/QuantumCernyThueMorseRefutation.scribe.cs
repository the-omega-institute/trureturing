using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class QuantumCernyThueMorseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/lee2026quantumcerny");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lee, Lee and Kjos-Hanssen (arXiv:2609.40154) define the quantum Cerny complexity qc(w) of a binary word w as the least dimension d for which two quantum channels on d x d density matrices and a start state make w the unique shortest synchronizing word, and conjecture that the Thue-Morse prefix 01101001 has qc = 2. No qubit instance has this word as its unique shortest synchronizing word, so the conjecture fails; with the authors' upper bound qc(w) <= 3 the value is 3.",
        H("The Thue-Morse prefix 01101001 needs more than one qubit"),
        Blocks(
            Node("apply", "The channel of a word", ApplyFormula(),
                "The letters act left to right: the empty word leaves the state unchanged, and the word a :: u first applies the channel of the letter a, then the channel of u. The channels are the completely positive trace-preserving maps on d x d matrices and the states are the positive semidefinite trace-one matrices.",
                "applyWord", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("reachable", "The reachable set", ReachableFormula(),
                "The reachable set is the set of images of the start state under the channels of all words.",
                "reachable", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sync", "Synchronizing words", SyncFormula(),
                "A word synchronizes the instance when its channel is constant on the reachable set.",
                "Synchronizing", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("unique", "Unique shortest synchronizing word", UniqueFormula(),
                "The word w synchronizes and no other word of length at most |w| does.",
                "UniqueShortestSync", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("instance", "Instances of dimension d", InstanceFormula(),
                "Some pair of channels on d x d matrices and some start state have w as their unique shortest synchronizing word.",
                "HasInstance", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("qc", "The quantum Cerny complexity", QcFormula(),
                "The least dimension d at least 1 with such an instance, as the infimum of a set of natural numbers.",
                "qc", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("word", "The Thue-Morse prefix", WordFormula(),
                "The first eight letters of the Thue-Morse word.",
                "thueMorsePrefix", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "Open problem 1 of the paper: the Thue-Morse prefix has quantum Cerny complexity 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("comp", "The linear map of a word", CompFormula(),
                "For two linear maps f(0), f(1) of a vector space V over a field K, the empty word gives the identity and the word a :: u gives the map of u after f(a).",
                "wordComp", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("lemma", "A dimension lemma for the Thue-Morse prefix", LemmaFormula(),
                "Let P, Q and T be the maps of 01101, 01 and 001. The image of P lies in the image of Q; if the two images had equal dimension they would coincide, and the map of 01001, which is T after Q, would agree on every vector with T after P, the map of 01101001, so it would vanish. Hence the image of Q has larger dimension than the image of P, which is at least 1 when P is nonzero. The map f(0) is not surjective, since the map of 01101001 is the map of 1101001 after f(0). So the image of Q, the image of f(0) under f(1), has dimension at most 2, hence exactly 2. The image of Q lies in the image of f(1); if they coincided, the map of 1101001 would vanish, since it is the map of 101001 after f(1) and the map of 01101001 is the map of 101001 after Q. So f(1) has rank 3, it is injective, and the map of 0110100 vanishes because f(1) after it is the map of 01101001.",
                "mortal_thueMorse", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The conjecture fails", Disp(new Formula.Not(F.Id("claim"))),
                "If the complexity were 2, the set defining it would contain 2, giving a qubit instance with 01101001 as unique shortest synchronizing word. Let V be the complex span of the differences of reachable states. A word synchronizes exactly when the linear map of its channel vanishes on V, and each channel maps V into itself. The differences of states have trace zero, so V lies in the span of three traceless 2 x 2 matrices and has dimension at most 3. Applying the dimension lemma to the two channels restricted to V shows that one of 01101, 01001, 1101001, 0110100 synchronizes, although each is shorter than 01101001.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-kjoshanssen-2026-quantum-cerny-thue-morse"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("qcerny-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(F.Id(name)), [.. arguments]);
    private static Formula Of(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NeTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Words() => Call("List", Fin(D(2)));
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Channels(Formula d) => Arrow(Fin(D(2)), Call("QuantumChannel", Fin(d), Fin(d)));
    private static Formula States(Formula d) => Call("DensityState", Fin(d));
    private static Formula Length(Formula u) => Seq(Bar, u, Bar);
    private static Formula Cons(Formula a, Formula u) => Seq(a, Sp, Colon, Colon, Sp, u);
    private static Formula WordList(params int[] letters)
    {
        var parts = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (var i = 0; i < letters.Length; i++)
        {
            if (i > 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(D(letters[i] == 0 ? (byte)0 : (byte)1));
        }
        parts.Add(CloseBracket);
        return Seq([.. parts]);
    }
    private static Formula Vars(params Formula[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(names[i]);
        }
        return Seq([.. parts]);
    }
    private static Formula Apply(Formula a, Formula u, Formula rho) => Call("applyWord", a, u, rho);
    private static Formula Sync(Formula u) => Call("Synchronizing", F.Id("A"), Seq(F.Id("rho"), Underscore, D(0)), u);

    private static Formula Instance(Formula body)
    {
        Formula d = F.Id("d"), a = F.Id("A"), rho0 = Seq(F.Id("rho"), Underscore, D(0));
        return All(d, Nat(), All(a, Channels(d), All(rho0, States(d), body)));
    }

    private static Formula ApplyFormula()
    {
        Formula d = F.Id("d"), a = F.Id("A"), rho = F.Id("rho"), x = F.Id("a"), u = F.Id("u");
        Formula empty = EqTo(Apply(a, Seq(OpenBracket, CloseBracket), rho), rho);
        Formula step = EqTo(Apply(a, Cons(x, u), rho), Apply(a, u, Call("mapState", Of(a, x), rho)));
        return Disp(All(d, Nat(), All(a, Channels(d), All(rho, States(d),
            And(empty, All(x, Fin(D(2)), All(u, Words(), step)))))));
    }

    private static Formula ReachableFormula()
    {
        Formula u = F.Id("u"), rho0 = Seq(F.Id("rho"), Underscore, D(0));
        Formula set = Seq(Esc, OpenBrace, Apply(F.Id("A"), u, rho0), Sp, Mid, Sp, u, Sp, Colon, Sp, Words(),
            Esc, CloseBrace);
        return Disp(Instance(EqTo(Call("reachable", F.Id("A"), rho0), set)));
    }

    private static Formula SyncFormula()
    {
        Formula w = F.Id("w"), rho = F.Id("rho"), rho1 = Seq(F.Id("rho"), Underscore, D(1)),
            rho0 = Seq(F.Id("rho"), Underscore, D(0)), d = F.Id("d");
        Formula body = Some(rho1, States(d), Seq(Forall, Sp, rho, Sp, InMacro, Sp,
            Call("reachable", F.Id("A"), rho0), Comma, Sp, EqTo(Apply(F.Id("A"), w, rho), rho1)));
        return Disp(Instance(All(w, Words(), Iff(Sync(w), body))));
    }

    private static Formula UniqueFormula()
    {
        Formula w = F.Id("w"), u = F.Id("u"), rho0 = Seq(F.Id("rho"), Underscore, D(0));
        Formula others = All(u, Words(), Imp(LeTo(Length(u), Length(w)), Imp(NeTo(u, w),
            new Formula.Not(Sync(u)))));
        return Disp(Instance(All(w, Words(),
            Iff(Call("UniqueShortestSync", F.Id("A"), rho0, w), And(Sync(w), others)))));
    }

    private static Formula InstanceFormula()
    {
        Formula d = F.Id("d"), w = F.Id("w"), a = F.Id("A"), rho0 = Seq(F.Id("rho"), Underscore, D(0));
        Formula body = Some(a, Channels(d), Some(rho0, States(d), Call("UniqueShortestSync", a, rho0, w)));
        return Disp(All(d, Nat(), All(w, Words(), Iff(Call("HasInstance", d, w), body))));
    }

    private static Formula QcFormula()
    {
        Formula d = F.Id("d"), w = F.Id("w");
        Formula set = Seq(Esc, OpenBrace, d, Sp, Colon, Sp, Nat(), Sp, Mid, Sp,
            And(LeTo(D(1), d), Call("HasInstance", d, w)), Esc, CloseBrace);
        return Disp(All(w, Words(), EqTo(Call("qc", w), Call("sInf", set))));
    }

    private static Formula WordFormula() =>
        Disp(EqTo(F.Id("thueMorsePrefix"), WordList(0, 1, 1, 0, 1, 0, 0, 1)));

    private static Formula ClaimFormula() =>
        Disp(Iff(F.Id("claim"), EqTo(Call("qc", F.Id("thueMorsePrefix")), D(2))));

    private static Formula CompFormula()
    {
        Formula k = F.Id("K"), v = F.Id("V"), f = F.Id("f"), x = F.Id("a"), u = F.Id("u");
        Formula maps = Arrow(Fin(D(2)), Call("End", k, v));
        Formula empty = EqTo(Call("wordComp", f, Seq(OpenBracket, CloseBracket)), Named(F.Id("id")));
        Formula step = EqTo(Call("wordComp", f, Cons(x, u)),
            Seq(Call("wordComp", f, u), Sp, Circ, Sp, Of(f, x)));
        Formula structure = And(Call("Field", k), Call("Module", k, v));
        return Disp(All(Vars(k, v), Call("Type"), Imp(structure, All(f, maps,
            And(empty, All(x, Fin(D(2)), All(u, Words(), step)))))));
    }

    private static Formula LemmaFormula()
    {
        Formula k = F.Id("K"), v = F.Id("V"), f = F.Id("f");
        Formula maps = Arrow(Fin(D(2)), Call("End", k, v));
        Formula zero(params int[] word) => EqTo(Call("wordComp", f, WordList(word)), D(0));
        Formula hyp = And(LeTo(Call("dim", k, v), D(3)), zero(0, 1, 1, 0, 1, 0, 0, 1));
        Formula concl = Or(Or(zero(0, 1, 1, 0, 1), zero(0, 1, 0, 0, 1)),
            Or(zero(1, 1, 0, 1, 0, 0, 1), zero(0, 1, 1, 0, 1, 0, 0)));
        Formula structure = And(And(Call("Field", k), Call("Module", k, v)), Call("FiniteDimensional", k, v));
        return Disp(All(Vars(k, v), Call("Type"), Imp(structure, All(f, maps, Imp(hyp, concl)))));
    }
}
