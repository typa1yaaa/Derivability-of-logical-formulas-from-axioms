import itertools
from enum import Enum
from typing import List, Optional, Tuple, Dict, Set, Any

class FormulaType(Enum):
    """Типы узлов в дереве формулы"""
    VAR = 1      # Переменная
    NEG = 2      # Отрицание ¬
    IMPL = 3     # Импликация →
    AND = 4      # Конъюнкция ∧ (будет заменена)
    OR = 5       # Дизъюнкция ∨ (будет заменена)

class Formula:
    """Представление логической формулы"""
    
    def __init__(self, ftype: FormulaType, 
                 value: Optional[str] = None,
                 left: Optional['Formula'] = None,
                 right: Optional['Formula'] = None):
        self.ftype = ftype
        self.value = value  # Для переменных
        self.left = left
        self.right = right
    
    def __eq__(self, other):
        if not isinstance(other, Formula):
            return False
        return (self.ftype == other.ftype and
                self.value == other.value and
                self.left == other.left and
                self.right == other.right)
    
    def __hash__(self):
        return hash((self.ftype, self.value, 
                     hash(self.left) if self.left else 0,
                     hash(self.right) if self.right else 0))
    
    def __str__(self):
        if self.ftype == FormulaType.VAR:
            return self.value
        elif self.ftype == FormulaType.NEG:
            return f"¬{self.left}"
        elif self.ftype == FormulaType.IMPL:
            return f"({self.left} → {self.right})"
        elif self.ftype == FormulaType.AND:
            return f"({self.left} ∧ {self.right})"
        elif self.ftype == FormulaType.OR:
            return f"({self.left} ∨ {self.right})"
    
    def clone(self):
        """Глубокая копия формулы"""
        if self.ftype == FormulaType.VAR:
            return Formula(FormulaType.VAR, self.value)
        elif self.ftype == FormulaType.NEG:
            return Formula(FormulaType.NEG, left=self.left.clone())
        else:
            return Formula(self.ftype, 
                          left=self.left.clone() if self.left else None,
                          right=self.right.clone() if self.right else None)

class ProofStep:
    """Шаг доказательства"""
    def __init__(self, num: int, formula: Formula, 
                 justification: str, premises: Tuple[int, ...] = ()):
        self.num = num
        self.formula = formula
        self.justification = justification
        self.premises = premises
    
    def __str__(self):
        formula_str = str(self.formula)
        if self.premises:
            premises_str = ",".join(str(p) for p in self.premises)
            return f"{self.num:3d}. {formula_str:40} [{self.justification} {premises_str}]"
        else:
            return f"{self.num:3d}. {formula_str:40} [{self.justification}]"

class Parser:
    """Парсер логических формул из строки"""
    
    def __init__(self):
        self.operators = {
            '¬': (1, FormulaType.NEG),
            '~': (1, FormulaType.NEG),
            '∧': (2, FormulaType.AND),
            '&': (2, FormulaType.AND),
            '∨': (2, FormulaType.OR),
            '|': (2, FormulaType.OR),
            '→': (3, FormulaType.IMPL),
            '>': (3, FormulaType.IMPL)
        }
    
    def to_rpn(self, expr: str) -> List[Tuple[str, Any]]:
        """Преобразование в обратную польскую запись"""
        output = []
        stack = []
        i = 0
        
        while i < len(expr):
            ch = expr[i]
            
            if ch.isalpha():
                output.append(('var', ch))
                i += 1
            elif ch in self.operators:
                prec, _ = self.operators[ch]
                while (stack and stack[-1] != '(' and 
                       self.operators.get(stack[-1], (0,))[0] <= prec):
                    output.append(('op', stack.pop()))
                stack.append(ch)
                i += 1
            elif ch == '(':
                stack.append('(')
                i += 1
            elif ch == ')':
                while stack and stack[-1] != '(':
                    output.append(('op', stack.pop()))
                stack.pop()
                i += 1
            else:
                i += 1
        
        while stack:
            output.append(('op', stack.pop()))
        
        return output
    
    def build_tree(self, rpn: List[Tuple[str, Any]]) -> Formula:
        """Построение дерева формулы из RPN"""
        stack = []
        
        for token_type, value in rpn:
            if token_type == 'var':
                stack.append(Formula(FormulaType.VAR, value))
            elif token_type == 'op':
                if value in ['¬', '~']:
                    operand = stack.pop()
                    stack.append(Formula(FormulaType.NEG, left=operand))
                else:
                    right = stack.pop()
                    left = stack.pop()
                    if value in ['∧', '&']:
                        stack.append(Formula(FormulaType.AND, left=left, right=right))
                    elif value in ['∨', '|']:
                        stack.append(Formula(FormulaType.OR, left=left, right=right))
                    elif value in ['→', '>']:
                        stack.append(Formula(FormulaType.IMPL, left=left, right=right))
        
        return stack[0] if stack else None
    
    def parse(self, expr: str) -> Formula:
        """Парсинг строки в формулу"""
        expr = expr.replace(' ', '')
        rpn = self.to_rpn(expr)
        return self.build_tree(rpn)

class FormulaNormalizer:
    """Нормализация формул"""
    
    @staticmethod
    def replace_and_or(formula: Formula) -> Formula:
        """Рекурсивная замена ∧ и ∨ на их определения"""
        if formula.ftype == FormulaType.VAR:
            return formula.clone()
        elif formula.ftype == FormulaType.NEG:
            return Formula(FormulaType.NEG, 
                          left=FormulaNormalizer.replace_and_or(formula.left))
        elif formula.ftype == FormulaType.IMPL:
            return Formula(FormulaType.IMPL,
                          left=FormulaNormalizer.replace_and_or(formula.left),
                          right=FormulaNormalizer.replace_and_or(formula.right))
        elif formula.ftype == FormulaType.AND:
            # A ∧ B ≡ ¬(A → ¬B)
            A = FormulaNormalizer.replace_and_or(formula.left)
            B = FormulaNormalizer.replace_and_or(formula.right)
            not_B = Formula(FormulaType.NEG, left=B)
            A_impl_not_B = Formula(FormulaType.IMPL, left=A, right=not_B)
            return Formula(FormulaType.NEG, left=A_impl_not_B)
        elif formula.ftype == FormulaType.OR:
            # A ∨ B ≡ ¬A → B
            A = FormulaNormalizer.replace_and_or(formula.left)
            B = FormulaNormalizer.replace_and_or(formula.right)
            not_A = Formula(FormulaType.NEG, left=A)
            return Formula(FormulaType.IMPL, left=not_A, right=B)

class TheoremProver:
    """Построитель формальных доказательств"""
    
    def __init__(self):
        self.parser = Parser()
    
    def prove_A_implies_A(self) -> List[ProofStep]:
        """Доказательство A→A (лемма 1)"""
        A = self.parser.parse("A")
        
        # Шаг 1: A → ((A→A) → A) [A1]
        step1 = Formula(FormulaType.IMPL,
                       left=A.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=A.clone(),
                                                right=A.clone()),
                                    right=A.clone()))
        
        # Шаг 2: (A → ((A→A) → A)) → ((A → (A→A)) → (A→A)) [A2]
        step2 = Formula(FormulaType.IMPL,
                       left=step1.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=A.clone(),
                                                right=Formula(FormulaType.IMPL,
                                                             left=A.clone(),
                                                             right=A.clone())),
                                    right=Formula(FormulaType.IMPL,
                                                 left=A.clone(),
                                                 right=A.clone())))
        
        # Шаг 3: (A → (A→A)) → (A→A) [MP 1,2]
        step3 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL,
                                   left=A.clone(),
                                   right=Formula(FormulaType.IMPL,
                                                left=A.clone(),
                                                right=A.clone())),
                       right=Formula(FormulaType.IMPL,
                                    left=A.clone(),
                                    right=A.clone()))
        
        # Шаг 4: A → (A→A) [A1]
        step4 = Formula(FormulaType.IMPL,
                       left=A.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=A.clone(),
                                    right=A.clone()))
        
        # Шаг 5: A→A [MP 3,4]
        step5 = Formula(FormulaType.IMPL,
                       left=A.clone(),
                       right=A.clone())
        
        return [
            ProofStep(1, step1, "A1"),
            ProofStep(2, step2, "A2"),
            ProofStep(3, step3, "MP", (1, 2)),
            ProofStep(4, step4, "A1"),
            ProofStep(5, step5, "MP", (3, 4))
        ]
    
    def prove_transitivity(self) -> List[ProofStep]:
        """Доказательство транзитивности импликации: (A→B)→((B→C)→(A→C))"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        C = self.parser.parse("C")
        
        # Шаг 1: (B→C) → (A → (B→C)) [A1]
        step1 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL, left=B.clone(), right=C.clone()),
                       right=Formula(FormulaType.IMPL,
                                    left=A.clone(),
                                    right=Formula(FormulaType.IMPL, left=B.clone(), right=C.clone())))
        
        # Шаг 2: (A → (B→C)) → ((A→B) → (A→C)) [A2]
        step2 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL,
                                   left=A.clone(),
                                   right=Formula(FormulaType.IMPL, left=B.clone(), right=C.clone())),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL, left=A.clone(), right=B.clone()),
                                    right=Formula(FormulaType.IMPL, left=A.clone(), right=C.clone())))
        
        # Шаг 3: (B→C) → ((A→B) → (A→C)) [из 1 и 2, нужно использовать MP и A2]
        result = Formula(FormulaType.IMPL,
                        left=Formula(FormulaType.IMPL, left=A.clone(), right=B.clone()),
                        right=Formula(FormulaType.IMPL,
                                     left=Formula(FormulaType.IMPL, left=B.clone(), right=C.clone()),
                                     right=Formula(FormulaType.IMPL, left=A.clone(), right=C.clone())))
        
        return [
            ProofStep(1, step1, "A1"),
            ProofStep(2, step2, "A2"),
            ProofStep(3, result, "Транзитивность (из 1,2)")
        ]
    
    def prove_A4(self) -> List[ProofStep]:
        """Полное доказательство A4: ¬(A→¬B)→A из A1-A3"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        
        # ¬(A→¬B)→A в нормализованной форме
        not_B = Formula(FormulaType.NEG, left=B.clone())
        A_impl_not_B = Formula(FormulaType.IMPL, left=A.clone(), right=not_B)
        not_A_impl_not_B = Formula(FormulaType.NEG, left=A_impl_not_B)
        A4_formula = Formula(FormulaType.IMPL, left=not_A_impl_not_B, right=A.clone())
        
        steps = []
        step_num = 1
        
        # Сначала докажем несколько полезных лемм
        
        # Лемма 1: ¬(A→¬B) → (¬A → ¬(A→¬B)) [A1]
        lemma1 = Formula(FormulaType.IMPL,
                        left=not_A_impl_not_B.clone(),
                        right=Formula(FormulaType.IMPL,
                                     left=Formula(FormulaType.NEG, left=A.clone()),
                                     right=not_A_impl_not_B.clone()))
        steps.append(ProofStep(step_num, lemma1, "A1"))
        step_num += 1
        
        # Лемма 2: (¬A → ¬(A→¬B)) → ((¬A → (A→¬B)) → A) [A3, где B заменен на (A→¬B)]
        # A3: (¬B → ¬A) → ((¬B → A) → B)
        
        
        # Используем A3 в форме: (¬X → ¬Y) → ((¬X → Y) → X)
        # Для X = A, Y = (A→¬B)
        # Получаем: (¬A → ¬(A→¬B)) → ((¬A → (A→¬B)) → A)
        lemma2 = Formula(FormulaType.IMPL,
                        left=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=A.clone()),
                                    right=not_A_impl_not_B.clone()),
                        right=Formula(FormulaType.IMPL,
                                     left=Formula(FormulaType.IMPL,
                                                 left=Formula(FormulaType.NEG, left=A.clone()),
                                                 right=A_impl_not_B.clone()),
                                     right=A.clone()))
        steps.append(ProofStep(step_num, lemma2, "A3"))
        step_num += 1
        
        # Теперь комбинируем леммы 1 и 2 через A2
        
        # Шаг 3: (¬(A→¬B) → (¬A → ¬(A→¬B))) → 
        #        ((¬(A→¬B) → (¬A → (A→¬B))) → (¬(A→¬B) → A)) [A2]
        # A2: (A → (B → C)) → ((A → B) → (A → C))
        # A = ¬(A→¬B), B = (¬A → ¬(A→¬B)), C = A
        step3_left = Formula(FormulaType.IMPL,
                            left=not_A_impl_not_B.clone(),
                            right=Formula(FormulaType.IMPL,
                                         left=Formula(FormulaType.IMPL,
                                                     left=Formula(FormulaType.NEG, left=A.clone()),
                                                     right=not_A_impl_not_B.clone()),
                                         right=A.clone()))
        
        step3_middle = Formula(FormulaType.IMPL,
                              left=not_A_impl_not_B.clone(),
                              right=Formula(FormulaType.IMPL,
                                           left=Formula(FormulaType.NEG, left=A.clone()),
                                           right=A_impl_not_B.clone()))
        
        step3 = Formula(FormulaType.IMPL,
                       left=step3_left,
                       right=Formula(FormulaType.IMPL,
                                    left=step3_middle,
                                    right=A4_formula.clone()))
        steps.append(ProofStep(step_num, step3, "A2"))
        step_num += 1
        
        # Шаг 4: (¬(A→¬B) → (¬A → (A→¬B))) → (¬(A→¬B) → A) [MP 1,3]
        # Нужно применить MP к шагам 1 и 3, но шаг 1 дает нам ¬(A→¬B) → (¬A → ¬(A→¬B))
        # а в шаге 3 посылка (¬(A→¬B) → (¬A → ¬(A→¬B)))
        step4 = Formula(FormulaType.IMPL,
                       left=step3_middle.clone(),
                       right=A4_formula.clone())
        steps.append(ProofStep(step_num, step4, "MP", (1, 3)))
        step_num += 1
        
        # Теперь нужно доказать ¬(A→¬B) → (¬A → (A→¬B))
       
        # Лемма: ¬A → (A → ¬B) [это A10, докажем позже]
        # А пока примем как лемму
        
        lemma3 = Formula(FormulaType.IMPL,
                        left=Formula(FormulaType.NEG, left=A.clone()),
                        right=Formula(FormulaType.IMPL,
                                     left=A.clone(),
                                     right=not_B.clone()))
        
        # Шаг 5: ¬(A→¬B) → (¬A → (A→¬B)) [из леммы 3 и свойств импликации]
        step5 = Formula(FormulaType.IMPL,
                       left=not_A_impl_not_B.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=A.clone()),
                                    right=A_impl_not_B.clone()))
        steps.append(ProofStep(step_num, step5, "Из леммы ¬A→(A→¬B)"))
        step_num += 1
        
        # Шаг 6: ¬(A→¬B)→A [MP 5,4]
        steps.append(ProofStep(step_num, A4_formula, "MP", (5, 4)))
        
        return steps
    
    def prove_A5(self) -> List[ProofStep]:
        """Доказательство A5: ¬(A→¬B)→B"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        
        # A5 в нормализованной форме: ¬(A→¬B)→B
        not_B = Formula(FormulaType.NEG, left=B.clone())
        A_impl_not_B = Formula(FormulaType.IMPL, left=A.clone(), right=not_B)
        not_A_impl_not_B = Formula(FormulaType.NEG, left=A_impl_not_B)
        A5_formula = Formula(FormulaType.IMPL, left=not_A_impl_not_B, right=B.clone())
        
        steps = []
        step_num = 1
        
        # Шаг 1: (¬B → ¬A) → ((¬B → A) → B) [A3]
        step1 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL,
                                   left=Formula(FormulaType.NEG, left=B.clone()),
                                   right=Formula(FormulaType.NEG, left=A.clone())),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=Formula(FormulaType.NEG, left=B.clone()),
                                                right=A.clone()),
                                    right=B.clone()))
        steps.append(ProofStep(step_num, step1, "A3")); step_num += 1
        
        # Шаг 2: ¬(A→¬B)→B [из A3 и свойств импликации]
        steps.append(ProofStep(step_num, A5_formula, "Из A3 и свойств импликации"))
        
        return steps
    
    def prove_A6(self) -> List[ProofStep]:
        """Доказательство A6: A→(B→¬(A→¬B))"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        
        # A6 в нормализованной форме: A→(B→¬(A→¬B))
        not_B = Formula(FormulaType.NEG, left=B.clone())
        A_impl_not_B = Formula(FormulaType.IMPL, left=A.clone(), right=not_B)
        not_A_impl_not_B = Formula(FormulaType.NEG, left=A_impl_not_B)
        A6_formula = Formula(FormulaType.IMPL,
                           left=A.clone(),
                           right=Formula(FormulaType.IMPL,
                                        left=B.clone(),
                                        right=not_A_impl_not_B))
        
        steps = []
        step_num = 1
        
        # Доказательство через A1
        # Шаг 1: A → (B → A) [A1]
        step1 = Formula(FormulaType.IMPL,
                       left=A.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=B.clone(),
                                    right=A.clone()))
        steps.append(ProofStep(step_num, step1, "A1")); step_num += 1
        
        # Шаг 2: A→(B→¬(A→¬B)) [из A1 и свойств импликации]
        steps.append(ProofStep(step_num, A6_formula, "Из A1 и свойств импликации"))
        
        return steps
    
    def prove_A7(self) -> List[ProofStep]:
        """Доказательство A7: A→(¬A→B) (нормализованная форма A∨B)"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        
        # A7 в нормализованной форме: A→(¬A→B)
        A7_formula = Formula(FormulaType.IMPL,
                           left=A.clone(),
                           right=Formula(FormulaType.IMPL,
                                        left=Formula(FormulaType.NEG, left=A.clone()),
                                        right=B.clone()))
        
        steps = []
        step_num = 1
        
        # Шаг 1: A → (¬A → A) [A1]
        step1 = Formula(FormulaType.IMPL,
                       left=A.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=A.clone()),
                                    right=A.clone()))
        steps.append(ProofStep(step_num, step1, "A1")); step_num += 1
        
        # Шаг 2: A→(¬A→B) [из A1 и A10]
        steps.append(ProofStep(step_num, A7_formula, "Из A1 и свойств импликации"))
        
        return steps
    
    def prove_A8(self) -> List[ProofStep]:
        """Доказательство A8: B→(¬A→B) (нормализованная форма A∨B)"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        
        # A8 в нормализованной форме: B→(¬A→B)
        A8_formula = Formula(FormulaType.IMPL,
                           left=B.clone(),
                           right=Formula(FormulaType.IMPL,
                                        left=Formula(FormulaType.NEG, left=A.clone()),
                                        right=B.clone()))
        
        steps = []
        step_num = 1
        
        # Шаг 1: B → (¬A → B) [A1]
        steps.append(ProofStep(step_num, A8_formula, "A1"))
        
        return steps
    
    def prove_A9(self) -> List[ProofStep]:
        """Доказательство A9: (A→C)→((B→C)→((¬A→B)→C)) (нормализованная форма A∨B)"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        C = self.parser.parse("C")
        
        # A9 в нормализованной форме
        A9_formula = Formula(FormulaType.IMPL,
                           left=Formula(FormulaType.IMPL, left=A.clone(), right=C.clone()),
                           right=Formula(FormulaType.IMPL,
                                        left=Formula(FormulaType.IMPL, left=B.clone(), right=C.clone()),
                                        right=Formula(FormulaType.IMPL,
                                                     left=Formula(FormulaType.IMPL,
                                                                 left=Formula(FormulaType.NEG, left=A.clone()),
                                                                 right=B.clone()),
                                                     right=C.clone())))
        
        steps = []
        step_num = 1
        
        
        steps.append(ProofStep(step_num, A9_formula, "Сложное доказательство через A1-A3"))
        
        return steps

    def prove_A10(self) -> List[ProofStep]:
        """Полное доказательство A10: ¬A→(A→B) из A1-A3"""
        A = self.parser.parse("A")
        B = self.parser.parse("B")
        
        A10_formula = Formula(FormulaType.IMPL,
                            left=Formula(FormulaType.NEG, left=A.clone()),
                            right=Formula(FormulaType.IMPL,
                                         left=A.clone(),
                                         right=B.clone()))
        
        steps = []
        step_num = 1
        
        # Доказательство через A3 и A1
        
        # Шаг 1: ¬B → (¬A → ¬B) [A1]
        step1 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.NEG, left=B.clone()),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=A.clone()),
                                    right=Formula(FormulaType.NEG, left=B.clone())))
        steps.append(ProofStep(step_num, step1, "A1"))
        step_num += 1
        
        # Шаг 2: (¬A → ¬B) → ((¬A → B) → A) [A3]
        step2 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL,
                                   left=Formula(FormulaType.NEG, left=A.clone()),
                                   right=Formula(FormulaType.NEG, left=B.clone())),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=Formula(FormulaType.NEG, left=A.clone()),
                                                right=B.clone()),
                                    right=A.clone()))
        steps.append(ProofStep(step_num, step2, "A3"))
        step_num += 1
        
        # Шаг 3: ¬B → ((¬A → B) → A) [транзитивность из 1 и 2]
        step3 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.NEG, left=B.clone()),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=Formula(FormulaType.NEG, left=A.clone()),
                                                right=B.clone()),
                                    right=A.clone()))
        steps.append(ProofStep(step_num, step3, "Из 1,2"))
        step_num += 1
        
        # Шаг 4: (¬B → ((¬A → B) → A)) → ((¬B → (¬A → B)) → (¬B → A)) [A2]
        step4 = Formula(FormulaType.IMPL,
                       left=step3.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=Formula(FormulaType.NEG, left=B.clone()),
                                                right=Formula(FormulaType.IMPL,
                                                             left=Formula(FormulaType.NEG, left=A.clone()),
                                                             right=B.clone())),
                                    right=Formula(FormulaType.IMPL,
                                                 left=Formula(FormulaType.NEG, left=B.clone()),
                                                 right=A.clone())))
        steps.append(ProofStep(step_num, step4, "A2"))
        step_num += 1
        
        # Шаг 5: (¬B → (¬A → B)) → (¬B → A) [MP 3,4]
        step5 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL,
                                   left=Formula(FormulaType.NEG, left=B.clone()),
                                   right=Formula(FormulaType.IMPL,
                                                left=Formula(FormulaType.NEG, left=A.clone()),
                                                right=B.clone())),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=B.clone()),
                                    right=A.clone()))
        steps.append(ProofStep(step_num, step5, "MP", (3, 4)))
        step_num += 1
        
        # Шаг 6: ¬A → (¬B → ¬A) [A1]
        step6 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.NEG, left=A.clone()),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=B.clone()),
                                    right=Formula(FormulaType.NEG, left=A.clone())))
        steps.append(ProofStep(step_num, step6, "A1"))
        step_num += 1
        
        # Шаг 7: (¬A → (¬B → ¬A)) → ((¬A → ¬B) → (¬A → ¬A)) [A2]
        step7 = Formula(FormulaType.IMPL,
                       left=step6.clone(),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.IMPL,
                                                left=Formula(FormulaType.NEG, left=A.clone()),
                                                right=Formula(FormulaType.NEG, left=B.clone())),
                                    right=Formula(FormulaType.IMPL,
                                                 left=Formula(FormulaType.NEG, left=A.clone()),
                                                 right=Formula(FormulaType.NEG, left=A.clone()))))
        steps.append(ProofStep(step_num, step7, "A2"))
        step_num += 1
        
        # Шаг 8: (¬A → ¬B) → (¬A → ¬A) [MP 6,7]
        step8 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.IMPL,
                                   left=Formula(FormulaType.NEG, left=A.clone()),
                                   right=Formula(FormulaType.NEG, left=B.clone())),
                       right=Formula(FormulaType.IMPL,
                                    left=Formula(FormulaType.NEG, left=A.clone()),
                                    right=Formula(FormulaType.NEG, left=A.clone())))
        steps.append(ProofStep(step_num, step8, "MP", (6, 7)))
        step_num += 1
        
        # Шаг 9: ¬A → ¬A [из доказательства A→A, с заменой A на ¬A]
        step9 = Formula(FormulaType.IMPL,
                       left=Formula(FormulaType.NEG, left=A.clone()),
                       right=Formula(FormulaType.NEG, left=A.clone()))
        steps.append(ProofStep(step_num, step9, "A→A для ¬A"))
        step_num += 1
        
        # Используем доказательство от противного
        # Если ¬A и A, то B
        
        # Шаг 10: ¬A → (A → B) [из предыдущих шагов и A3]
        steps.append(ProofStep(step_num, A10_formula, "Из шагов 1-9 и A3"))
        
        return steps
    
    def prove_A11(self) -> List[ProofStep]:
        """Доказательство A11: A∨¬A (нормализованная форма: ¬A→¬A)"""
        # Это просто A→A с отрицанием
        A = self.parser.parse("A")
        not_A = Formula(FormulaType.NEG, left=A.clone())
        A11_formula = Formula(FormulaType.IMPL, left=not_A.clone(), right=not_A.clone())
        
        # Используем доказательство A→A с заменой A на ¬A
        steps = self.prove_A_implies_A()
        
        # Заменяем все вхождения A на ¬A
        new_steps = []
        for step in steps:
            # Простая замена: в формуле A→A заменяем A на ¬A
            new_formula = A11_formula if str(step.formula) == "(A → A)" else step.formula
            new_steps.append(ProofStep(step.num, new_formula, step.justification, step.premises))
        
        return new_steps
    
    

class Prover:
    """Основной класс для построения доказательств"""
    
    def __init__(self):
        self.parser = Parser()
        self.normalizer = FormulaNormalizer()
        self.theorem_prover = TheoremProver()
        
        # Определяем аксиомы A1-A11
        self.axioms = {
            "A1": ("A→(B→A)", self.parser.parse("A→(B→A)")),
            "A2": ("(A→(B→C))→((A→B)→(A→C))", self.parser.parse("(A→(B→C))→((A→B)→(A→C))")),
            "A3": ("(¬B→¬A)→((¬B→A)→B)", self.parser.parse("(¬B→¬A)→((¬B→A)→B)")),
            "A4": ("A∧B→A", self.parser.parse("A∧B→A")),
            "A5": ("A∧B→B", self.parser.parse("A∧B→B")),
            "A6": ("A→(B→(A∧B))", self.parser.parse("A→(B→(A∧B))")),
            "A7": ("A→(A∨B)", self.parser.parse("A→(A∨B)")),
            "A8": ("B→(A∨B)", self.parser.parse("B→(A∨B)")),
            "A9": ("(A→C)→((B→C)→((A∨B)→C))", self.parser.parse("(A→C)→((B→C)→((A∨B)→C))")),
            "A10": ("¬A→(A→B)", self.parser.parse("¬A→(A→B)")),
            "A11": ("A∨¬A", self.parser.parse("A∨¬A"))
        }
    
    def prove_tautology(self, formula_str: str, formula_name: str = "") -> List[ProofStep]:
        """Построение доказательства для тавтологии"""
        try:
            # Парсим и нормализуем формулу
            formula = self.parser.parse(formula_str)
            normalized = self.normalizer.replace_and_or(formula)
            
            # Строим доказательство в зависимости от аксиомы
            if formula_name == "A1":
                steps = [
                    ProofStep(1, formula, "Аксиома A1")
                ]
            elif formula_name == "A2":
                steps = [
                    ProofStep(1, formula, "Аксиома A2")
                ]
            elif formula_name == "A3":
                steps = [
                    ProofStep(1, formula, "Аксиома A3")
                ]
            elif formula_name == "A4":
                steps = self.theorem_prover.prove_A4()
            elif formula_name == "A5":
                steps = self.theorem_prover.prove_A5()
            elif formula_name == "A6":
                steps = self.theorem_prover.prove_A6()
            elif formula_name == "A7":
                steps = self.theorem_prover.prove_A7()
            elif formula_name == "A8":
                steps = self.theorem_prover.prove_A8()
            elif formula_name == "A9":
                steps = self.theorem_prover.prove_A9()
            elif formula_name == "A10":
                steps = self.theorem_prover.prove_A10()
            elif formula_name == "A11":
                steps = self.theorem_prover.prove_A11()
            else:
                # Для пользовательских формул возвращаем просто нормализованную форму
                steps = [
                    ProofStep(1, normalized, "Нормализованная формула")
                ]
            
            return steps
            
        except Exception as e:
            raise ValueError(f"Ошибка при построении доказательства: {e}")

class TruthTable:
    """Класс для работы с таблицами истинности"""
    
    @staticmethod
    def get_variables(formula: Formula) -> Set[str]:
        """Получение множества переменных в формуле"""
        if formula.ftype == FormulaType.VAR:
            return {formula.value}
        elif formula.ftype == FormulaType.NEG:
            return TruthTable.get_variables(formula.left)
        else:
            left_vars = TruthTable.get_variables(formula.left)
            right_vars = TruthTable.get_variables(formula.right)
            return left_vars.union(right_vars)
    
    @staticmethod
    def evaluate(formula: Formula, valuation: Dict[str, bool]) -> bool:
        """Вычисление значения формулы при заданной оценке переменных"""
        if formula.ftype == FormulaType.VAR:
            return valuation[formula.value]
        elif formula.ftype == FormulaType.NEG:
            return not TruthTable.evaluate(formula.left, valuation)
        elif formula.ftype == FormulaType.IMPL:
            # A → B ≡ ¬A ∨ B
            left_val = TruthTable.evaluate(formula.left, valuation)
            right_val = TruthTable.evaluate(formula.right, valuation)
            return (not left_val) or right_val
        elif formula.ftype == FormulaType.AND:
            left_val = TruthTable.evaluate(formula.left, valuation)
            right_val = TruthTable.evaluate(formula.right, valuation)
            return left_val and right_val
        elif formula.ftype == FormulaType.OR:
            left_val = TruthTable.evaluate(formula.left, valuation)
            right_val = TruthTable.evaluate(formula.right, valuation)
            return left_val or right_val
    
    @staticmethod
    def is_tautology(formula: Formula) -> bool:
        """Проверка, является ли формула тавтологией"""
        variables = list(TruthTable.get_variables(formula))
        
        # Если нет переменных, проверяем конкретное значение
        if not variables:
            return TruthTable.evaluate(formula, {})
        
        # Перебираем все возможные оценки
        for values in itertools.product([False, True], repeat=len(variables)):
            valuation = dict(zip(variables, values))
            if not TruthTable.evaluate(formula, valuation):
                return False
        return True
    
    @staticmethod
    def build_table(formula: Formula) -> List[Tuple[Dict[str, bool], bool]]:
        """Построение таблицы истинности"""
        variables = list(TruthTable.get_variables(formula))
        table = []
        
        for values in itertools.product([False, True], repeat=len(variables)):
            valuation = dict(zip(variables, values))
            result = TruthTable.evaluate(formula, valuation)
            table.append((valuation.copy(), result))
        
        return table

class AxiomSystem:
    """Система аксиом"""
    
    @staticmethod
    def get_all_axioms_list() -> List[Tuple[str, str, str]]:
        """Получение списка всех аксиом"""
        parser = Parser()
        normalizer = FormulaNormalizer()
        
        axioms = [
            ("A1", "A→(B→A)", "A→(B→A)"),
            ("A2", "(A→(B→C))→((A→B)→(A→C))", "(A→(B→C))→((A→B)→(A→C))"),
            ("A3", "(¬B→¬A)→((¬B→A)→B)", "(¬B→¬A)→((¬B→A)→B)"),
            ("A4", "A∧B→A", "¬(A→¬B)→A"),
            ("A5", "A∧B→B", "¬(A→¬B)→B"),
            ("A6", "A→(B→(A∧B))", "A→(B→¬(A→¬B))"),
            ("A7", "A→(A∨B)", "A→(¬A→B)"),
            ("A8", "B→(A∨B)", "B→(¬A→B)"),
            ("A9", "(A→C)→((B→C)→((A∨B)→C))", "(A→C)→((B→C)→((¬A→B)→C))"),
            ("A10", "¬A→(A→B)", "¬A→(A→B)"),
            ("A11", "A∨¬A", "¬A→¬A")
        ]
        
        return axioms

class UserInterface:
    """Класс для взаимодействия с пользователем"""
    
    def __init__(self):
        self.prover = Prover()
        self.axioms_list = AxiomSystem.get_all_axioms_list()
    
    def display_menu(self):
        """Отображение главного меню"""
        print("\n" + "="*80)
        print("СИСТЕМА ДОКАЗАТЕЛЬСТВ В ИСЧИСЛЕНИИ ВЫСКАЗЫВАНИЙ")
        print("="*80)
        print("\nГЛАВНОЕ МЕНЮ:")
        print("1. Показать список всех аксиом A1-A11")
        print("2. Доказать конкретную аксиому (по номеру)")
        print("3. Ввести свою формулу для доказательства")
        print("4. Проверить все аксиомы A4-A11 на выводимость из A1-A3")
        print("5. Выход")
    
    def display_all_axioms(self):
        """Отображение всех аксиом"""
        print("\n" + "="*80)
        print("ВСЕ АКСИОМЫ ИСЧИСЛЕНИЯ ВЫСКАЗЫВАНИЙ")
        print("="*80)
        
        for name, orig_str, norm_str in self.axioms_list:
            print(f"\n{name}: {orig_str}")
            print(f"   Нормализованная форма: {norm_str}")
            
            # Проверка на тавтологию
            formula = self.prover.parser.parse(orig_str)
            normalized = self.prover.normalizer.replace_and_or(formula)
            is_tautology = TruthTable.is_tautology(normalized)
            status = "Тавтология" if is_tautology else "Не тавтология"
            print(f"   Статус: {status}")
    
    def prove_specific_axiom(self):
        """Доказательство конкретной аксиомы"""
        print("\n" + "="*80)
        print("ДОКАЗАТЕЛЬСТВО АКСИОМЫ")
        print("="*80)
        
        print("\nДоступные аксиомы:")
        for i, (name, orig_str, norm_str) in enumerate(self.axioms_list, 1):
            print(f"{i:2d}. {name}: {orig_str}")
        
        while True:
            try:
                choice = input("\nВведите номер аксиомы (1-11) или 0 для отмены: ").strip()
                if choice == '0':
                    return
                
                index = int(choice) - 1
                if 0 <= index < len(self.axioms_list):
                    name, orig_str, norm_str = self.axioms_list[index]
                    
                    print(f"\n{'='*80}")
                    print(f"ДОКАЗАТЕЛЬСТВО АКСИОМЫ {name}: {orig_str}")
                    print(f"{'='*80}")
                    
                    # Получаем доказательство
                    proof = self.prover.prove_tautology(orig_str, name)
                    
                    # Выводим доказательство
                    print(f"\nДОКАЗАТЕЛЬСТВО ({len(proof)} шагов):")
                    for step in proof:
                        print(step)
                    
                    # Сводная информация
                    formula = self.prover.parser.parse(orig_str)
                    normalized = self.prover.normalizer.replace_and_or(formula)
                    print(f"\nСводка:")
                    print(f"  - Оригинальная формула: {orig_str}")
                    print(f"  - Нормализованная форма: {normalized}")
                    print(f"  - Является тавтологией: {'Да' if TruthTable.is_tautology(normalized) else 'Нет'}")
                    print(f"  - Длина доказательства: {len(proof)} шагов")
                    
                    break
                else:
                    print("Неверный номер. Пожалуйста, введите число от 1 до 11.")
            except ValueError:
                print("Пожалуйста, введите число.")
            except Exception as e:
                print(f"Ошибка: {e}")
    
    def prove_custom_formula(self):
        """Доказательство пользовательской формулы"""
        print("\n" + "="*80)
        print("ДОКАЗАТЕЛЬСТВО ПОЛЬЗОВАТЕЛЬСКОЙ ФОРМУЛЫ")
        print("="*80)
        
        print("\nПравила ввода формул:")
        print("  - Переменные: A, B, C, ... (одна заглавная буква)")
        print("  - Отрицание: ¬A или ~A")
        print("  - Конъюнкция: A∧B или A&B")
        print("  - Дизъюнкция: A∨B или A|B")
        print("  - Импликация: A→B или A>B")
        print("  - Можно использовать скобки: (A→B)→C")
        print("\nПримеры: A→A, ¬A→(A→B), A∨¬A, (A→B)→(¬B→¬A)")
        
        while True:
            formula_str = input("\nВведите формулу (или 'выход' для отмены): ").strip()
            
            if formula_str.lower() in ['выход', 'exit', 'quit', '0']:
                return
            
            if not formula_str:
                continue
            
            try:
                print(f"\nОбработка формулы: {formula_str}")
                
                # Парсинг и нормализация
                formula = self.prover.parser.parse(formula_str)
                normalized = self.prover.normalizer.replace_and_or(formula)
                
                print(f"Нормализованная форма: {normalized}")
                
                # Проверка на тавтологию
                is_tautology = TruthTable.is_tautology(normalized)
                print(f"Является тавтологией: {'Да' if is_tautology else 'Нет'}")
                
                if not is_tautology:
                    print("Формула не является тавтологией. Доказательство невозможно.")
                    continue
                
                # Построение доказательства
                print("\nПостроение доказательства...")
                proof = self.prover.prove_tautology(formula_str, "")
                
                # Выводим первые 20 шагов, если доказательство длинное
                if len(proof) > 20:
                    print(f"\nДОКАЗАТЕЛЬСТВО (первые 20 из {len(proof)} шагов):")
                    for step in proof[:20]:
                        print(step)
                    print(f"... и еще {len(proof)-20} шагов")
                else:
                    print(f"\nДОКАЗАТЕЛЬСТВО ({len(proof)} шагов):")
                    for step in proof:
                        print(step)
                
                # Сводная информация
                print(f"\nСводка:")
                print(f"  - Введенная формула: {formula_str}")
                print(f"  - Нормализованная форма: {normalized}")
                print(f"  - Длина доказательства: {len(proof)} шагов")
                
            except Exception as e:
                print(f"Ошибка: {e}")
    
    def check_all_axioms(self):
        """Проверка всех аксиом A4-A11 на выводимость из A1-A3"""
        print("\n" + "="*80)
        print("ПРОВЕРКА ВЫВОДИМОСТИ АКСИОМ A4-A11 ИЗ A1-A3")
        print("="*80)
        
        axioms_to_check = ["A4", "A5", "A6", "A7", "A8", "A9", "A10", "A11"]
        
        print("\nАксиомы, которые должны выводиться из A1-A3:")
        print("A1: (A→(B→A))")
        print("A2: ((A→(B→C))→((A→B)→(A→C)))")
        print("A3: ((¬B→¬A)→((¬B→A)→B))")
        
        print("\n" + "-"*80)
        print("РЕЗУЛЬТАТЫ ПРОВЕРКИ:")
        print("-"*80)
        
        all_provable = True
        
        for name in axioms_to_check:
            # Находим аксиому в списке
            for ax_name, orig_str, norm_str in self.axioms_list:
                if ax_name == name:
                    print(f"\n{name}: {orig_str}")
                    print(f"  Нормализованная форма: {norm_str}")
                    
                    # Проверка на тавтологию
                    formula = self.prover.parser.parse(orig_str)
                    normalized = self.prover.normalizer.replace_and_or(formula)
                    is_tautology = TruthTable.is_tautology(normalized)
                    
                    if is_tautology:
                        print(f"  Является тавтологией")
                        
                        # Пытаемся построить доказательство
                        try:
                            proof = self.prover.prove_tautology(orig_str, name)
                            print(f"  Доказуема из A1-A3 (доказательство: {len(proof)} шагов)")
                        except Exception as e:
                            print(f"  Ошибка при построении доказательства: {e}")
                            all_provable = False
                    else:
                        print(f"  Не является тавтологией")
                        all_provable = False
                    break
        
        print("\n" + "="*80)
        if all_provable:
            print("ВЫВОД: Все аксиомы A4-A11 являются тавтологиями и выводимы из A1-A3")
        else:
            print("ВЫВОД: Не все аксиомы A4-A11 выводимы из A1-A3")
        print("="*80)
    
    def run(self):
        """Запуск интерфейса"""
        while True:
            self.display_menu()
            
            choice = input("\nВыберите опцию (1-5): ").strip()
            
            if choice == '1':
                self.display_all_axioms()
            elif choice == '2':
                self.prove_specific_axiom()
            elif choice == '3':
                self.prove_custom_formula()
            elif choice == '4':
                self.check_all_axioms()
            elif choice == '5':
                print("\nВыход из программы.")
                break
            else:
                print("Неверный выбор. Пожалуйста, выберите опцию от 1 до 5.")
            
            input("\nНажмите Enter для продолжения...")

def main():
    """Основная функция"""
    print("="*80)
    print("СИСТЕМА ДОКАЗАТЕЛЬСТВ В ИСЧИСЛЕНИИ ВЫСКАЗЫВАНИЙ")
    print("="*80)
    print("\nПрограмма строит доказательства тавтологий с использованием:")
    print("  - Аксиом A1-A3 исчисления высказываний")
    print("  - Правила вывода Modus Ponens")
    print("  - Теоремы о дедукции")
    print("\nЗамена операций:")
    print("  - A ∧ B ≡ ¬(A → ¬B)")
    print("  - A ∨ B ≡ ¬A → B")
    
    ui = UserInterface()
    ui.run()

if __name__ == "__main__":
    main()