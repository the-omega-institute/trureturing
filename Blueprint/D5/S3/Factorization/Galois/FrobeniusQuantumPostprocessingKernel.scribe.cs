using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class FrobeniusQuantumPostprocessingKernelDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/Galois/FrobeniusQuantumPostprocessingKernel."
            + "frobenius_quantum_postprocessing_kernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius-observer fibers survive quantum encoding and deterministic observation.",
        H("Frobenius Quantum Postprocessing Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frobenius-quantum-postprocessing-kernel"),
                DeclarationHandle.Create(Declaration),
                H("Postprocessing preserves every Frobenius-observer fiber"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public source object is the canonical tagged Frobenius observer "
                            + "on rational primes. Its unramified predicate and Frobenius "
                            + "representatives remain explicit parameters.")),
                    Paragraph(Text(
                        "An arbitrary encoding maps the complete tagged output to a quantum "
                            + "state, and an arbitrary deterministic observation maps that "
                            + "state to its final signature. Equality in the source kernel is "
                            + "preserved by both compositions.")),
                    Paragraph(Text(
                        "The proof directly applies Mathlib's factor-through composition law; "
                            + "no parallel observer or postprocessing primitive is introduced."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula group = F.Id("G");
        Formula primes = F.Id("Primes");
        Formula quantumState = F.Id("Q");
        Formula observation = F.Id("O");
        Formula unramified = F.Id("U");
        Formula frobenius = F.Id("Frob");
        Formula prime = F.Id("p");
        Formula encode = F.Id("eta");
        Formula observe = F.Id("Sigma");
        Formula classes = Call("ConjClasses", group);
        Formula taggedClasses = Call("Option", classes);
        Formula sourceObserver = Call("galoisPrimeObserver", unramified, frobenius);
        Formula composedObserver = Seq(observe, Sp, Circ, Sp, encode, Sp, Circ, Sp,
            sourceObserver);
        Formula frobeniusType = Seq(
            Forall, Sp, Typed(prime, primes), Comma, Sp,
            Apply(unramified, prime), Sp, To, Sp, group);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(group, type), Comma, Sp,
            Typed(quantumState, type), Comma, Sp,
            Typed(observation, type), Comma, RowBreak, Grp(),
            OpenBracket, Call("Monoid", group), CloseBracket, Comma, Sp,
            Typed(unramified, Arrow(primes, proposition)), Comma, RowBreak, Grp(),
            Typed(frobenius, frobeniusType), Comma, RowBreak, Grp(),
            Typed(encode, Arrow(taggedClasses, quantumState)), Comma, Sp,
            Typed(observe, Arrow(quantumState, observation)), Comma, RowBreak, Grp(),
            Call("ker", sourceObserver), Sp, Subseteq, Sp,
            Call("ker", composedObserver), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
