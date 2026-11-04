using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class JenzerPermutedRotorLoopWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords.";
    private const string Note = "D5/L/QuadraticForms/jenzer2026starorderedrotorloops";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced exterior words cancel odd full-support coefficients.", H("JenzerPermutedRotorLoopWords"),
        Blocks(
            Describe.Lean(DescribeId.Create("chain-expansion"), DeclarationHandle.Create(Prefix + "chain_expansion"), H("Subset expansion of the chain"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Distributing the ordered rotor product gives one increasing product for each subset, weighted by a. This expansion needs no anticommutation assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("subsetproduct-square"), DeclarationHandle.Create(Prefix + "subsetProduct_square"), H("Square of an increasing subset product"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The square depends only on the subset size. Nat.div is natural-number division. This is the Square of a Subset Product identity in Jenzer, Lemma 3.2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coefficient-complement"), DeclarationHandle.Create(Prefix + "coefficient_complement"), H("Complementary subset coefficients"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Multiplying coefficients for complementary subsets selects one sine and one cosine at every index, including when one of them is zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("return-expansion"), DeclarationHandle.Create(Prefix + "return_expansion"), H("Subset expansion of the return product"),
                StatementSource.FromAuthor(Disp(Formula3())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Reversion contributes one minus sign per selected bivector. Sorting the return order contributes the inversion parity on that subset. Every factor is retained in the coefficient; this is the return-product subset expansion and inversion-sign identity in the proof of Jenzer Theorem 5.5, before the star condition is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complementbridge-canonical-complementary-trace"), DeclarationHandle.Create(Prefix + "canonical_complementary_trace"), H("Complementary scalar pairs and exterior coefficients"),
                StatementSource.FromAuthor(Disp(Formula4())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For complementary supports, the Clifford sign is the top exterior coefficient of the corresponding pair. No cyclicity of the linear functional is required here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complementbridge-canonical-exterior-top"), DeclarationHandle.Create(Prefix + "canonical_exterior_top"), H("Top exterior coefficients require complementary supports"),
                StatementSource.FromAuthor(Disp(Formula5())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Repeated generators annihilate an exterior word, while a support missing an index cannot have the top coefficient. Thus only complementary supports contribute."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complementbridge-complement-ne-self"), DeclarationHandle.Create(Prefix + "complement_ne_self"), H("A nonempty index set has no self-complementary subset"),
                StatementSource.FromAuthor(Disp(Formula6())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("At any chosen index, membership in a subset is the negation of membership in its complement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exteriorsum-signed-top-sum-zero"), DeclarationHandle.Create(Prefix + "signed_top_sum_zero"), H("Cancellation of the odd full-support coefficient"),
                StatementSource.FromAuthor(Disp(Formula7())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The balanced exterior word has even parity for every permutation. Its odd top coefficient vanishes; expansion identifies that coefficient with the displayed double sum."))), DescribeRole.Theorem))));

    private static Formula Formula0() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), All(X("theta"), Arrow(Call("Fin", X("k")), Real), Equal(Call("chain", X("B"), X("theta")), Summation(X("S"), Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "powerset"), Smul(Call("a", X("theta"), X("S")), Call("subsetProduct", X("B"), X("S"))))))))))));

    private static Formula Formula1() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), ImpliesFormula(Call("AnticommutingUnitFamily", X("q"), X("k"), X("B")), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(Multiply(Call("subsetProduct", X("B"), X("S")), Call("subsetProduct", X("B"), X("S"))), Smul(Power(Cast(Negative(D(1)), Real), Call("Nat.div", Multiply(Member(X("S"), "card"), Add(Member(X("S"), "card"), D(1))), D(2))), Cast(D(1), Call("CliffordAlgebra", X("q")))))))))))));

    private static Formula Formula2() => All(X("k"), Nat, All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(Multiply(Call("a", X("theta"), X("S")), Call("a", X("theta"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S")))), Product(X("i"), Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), Multiply(Call("s", X("theta"), X("i")), Call("c", X("theta"), X("i"))))))));

    private static Formula Formula3() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), ImpliesFormula(Call("AnticommutingUnitFamily", X("q"), X("k"), X("B")), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), Equal(Call("returnProduct", X("B"), X("theta"), X("tau")), Summation(X("S"), Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "powerset"), Smul(Multiply(Multiply(Power(Cast(Negative(D(1)), Real), Member(X("S"), "card")), Power(Cast(Negative(D(1)), Real), Call("inversionCount", X("tau"), X("S")))), Call("a", X("theta"), X("S"))), Call("subsetProduct", X("B"), X("S"))))))))))))));

    private static Formula Formula4() => All(X("A"), TypeStar, Instance(Call("Ring", X("A")), Instance(Call("Algebra", Real, X("A")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), X("A")), ImpliesFormula(All(X("i"), Call("Fin", X("k")), All(X("j"), Call("Fin", X("k")), ImpliesFormula(NotEqual(X("i"), X("j")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("j"))), Negative(Multiply(App(X("B"), X("j")), App(X("B"), X("i")))))))), All(X("t"), Call("LinearMap", Real, X("A"), Real), All(X("b"), Call("Module.Basis", Call("Fin", X("k")), Real, Arrow(Call("Fin", X("k")), Real)), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(App(X("t"), Multiply(Member(App(Member(App(Member(X("S"), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod"), Member(App(Member(App(Member(SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S")), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod"))), Multiply(App(App(Member(Member(X("b"), "ExteriorAlgebra"), "repr"), Multiply(App(Member(X("b"), "ExteriorAlgebra"), X("S")), App(Member(X("b"), "ExteriorAlgebra"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S"))))), Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k"))))), App(X("t"), Member(App(Member(App(Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod")))))))))))));

    private static Formula Formula5() => All(X("k"), Nat, All(X("b"), Call("Module.Basis", Call("Fin", X("k")), Real, Arrow(Call("Fin", X("k")), Real)), All(X("S"), Call("Finset", Call("Fin", X("k"))), All(X("T"), Call("Finset", Call("Fin", X("k"))), ImpliesFormula(NotEqual(X("T"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S"))), Equal(App(App(Member(Member(X("b"), "ExteriorAlgebra"), "repr"), Multiply(App(Member(X("b"), "ExteriorAlgebra"), X("S")), App(Member(X("b"), "ExteriorAlgebra"), X("T")))), Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k"))))), D(0)))))));

    private static Formula Formula6() => All(X("k"), Nat, ImpliesFormula(LessEqual(D(1), X("k")), All(X("S"), Call("Finset", Call("Fin", X("k"))), NotEqual(X("S"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S"))))));

    private static Formula Formula7() => All(X("k"), Nat, All(X("b"), Call("Module.Basis", Call("Fin", X("k")), Real, Arrow(Call("Fin", X("k")), Real)), All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), ImpliesFormula(Call("Odd", X("k")), Equal(Summation(X("S"), Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "powerset"), Summation(X("T"), Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "powerset"), Multiply(Multiply(Power(Cast(Negative(D(1)), Real), Member(X("T"), "card")), Power(Cast(Negative(D(1)), Real), Call("inversionCount", X("tau"), X("T")))), App(App(Member(Member(X("b"), "ExteriorAlgebra"), "repr"), Multiply(App(Member(X("b"), "ExteriorAlgebra"), X("S")), App(Member(X("b"), "ExteriorAlgebra"), X("T")))), Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))))))), D(0))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Type => X("Type");
    private static Formula TypeStar => Seq(Type, Star);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Real => Seq(Mathbb, Grp(X("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string name) => Seq(name.Split('.').Select((part, index) =>
        index == 0 ? Seq(Operatorname, Grp(X(part))) : Seq(Dot, Operatorname, Grp(X(part)))).ToArray());
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula App(Formula function, params Formula[] args) => args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Member(Formula value, string name) => Seq(Parenthesized(value), Dot, Name(name));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Arrow(Formula source, Formula target) => Parenthesized(Seq(source, Sp, To, Sp, target));
    private static Formula Fn(Formula name, Formula body) => Parenthesized(Seq(Name("fun"), Sp, name, Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, Parenthesized(right));
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) => new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula SetDifference(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Setminus, Sp, Parenthesized(right));
    private static Formula Product(Formula name, Formula set, Formula body) => Seq(new Formula.Subscript(Prod, Seq(name, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Summation(Formula name, Formula set, Formula body) => Seq(new Formula.Subscript(Sum, Seq(name, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
}
