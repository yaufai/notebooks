from typing import List, TypeVar, Union, Tuple
from abc    import ABC, abstractmethod
from functools import reduce

# Definition of Infinity
inf  = float("inf")
Edge = Tuple[int, int]


T = TypeVar("T")

class TropicalPoint(ABC):
    value: T
    def __lt__(self, another: "TropicalPoint") -> bool:
        return not self >= another
    
    def __gt__(self, another: "TropicalPoint") -> bool:
        return not self <= another
    
    @abstractmethod
    def __ge__(self, another: "TropicalPoint") -> bool:
        raise NotImplementedError()
    
    @abstractmethod
    def __le__(self, another: "TropicalPoint") -> bool:
        raise NotImplementedError()
    
    def __add__(self, another: "TropicalPoint") -> "TropicalPoint":
        if another >= self:
            return self
        else:
            return another
    
    @abstractmethod
    def __mul__(self, another: "TropicalPoint") -> "TropicalPoint":
        raise NotImplementedError()
    
    def __str__(self) -> str:
        return str(self.value)

class Weight(TropicalPoint):
    def __init__(self, value: float) -> None:
        self.value = value
    
    def __le__(self, another: "Weight") -> bool:
        return self.value.__le__(another.value)
    
    def __ge__(self, another: "Weight") -> bool:
        return self.value.__ge__(another.value)
    
    def __mul__(self, another: "Weight") -> "Weight":
        return Weight(self.value + another.value)

class Path(TropicalPoint):
    def __init__(self, value: Union[List[Edge], None], cost: float) -> None:
        self.value = value
        self.cost  = cost
    
    def __le__(self, another: "Path") -> bool:
        return self.cost.__le__(another.cost)
    
    def __ge__(self, another: "Path") -> bool:
        return self.cost.__ge__(another.cost)
    
    def __mul__(self, another: "Path") -> "Path":
        if (self.value == None) or (another.value == None):
            added_value = None
        else:
            added_value = self.value + another.value
        return Path(added_value, self.cost + another.cost)

class TropicalVector:
    def __init__(self, vector: List[TropicalPoint]) -> None:
        self.vector = vector

    def __len__(self) -> int:
        return len(self.vector)

    def __getitem__(self, key: int) -> TropicalPoint:
        return self.vector[key]
    
    def __add__(self, vector: "TropicalVector") -> "TropicalVector":
        if len(self) == len(vector):
            return TropicalVector([ self[i] + vector[i] for i in range(len(self)) ])
        else:
            raise ValueError()

    # Inner product
    def __mul__(self, vector: "TropicalVector") -> TropicalPoint:
        if len(self) == len(vector):
            return min([ self[i] * vector[i] for i in range(len(self)) ])
        else:
            raise ValueError()
    
    def __str__(self) -> str:
        return str(list(map(str, self.vector))).replace("'", "").replace('"', "")

class TropicalMatrix:
    def __init__(self, matrix: List[TropicalVector]) -> None:
        self.matrix = matrix
    
    def __add__(self, matrix: "TropicalMatrix") -> "TropicalMatrix":
        if len(self.matrix) == len(matrix.matrix):
            return TropicalMatrix(
                [ self.matrix[i] + matrix.matrix[i]
                for i in range(len(self.matrix)) ]
            )
        else:
            raise ValueError()
    
    def __mul__(self, adjacency: "TropicalMatrix") -> "TropicalMatrix":
        def compute_line(line_idx: int) -> TropicalVector:
            line = self.matrix[line_idx]
            return TropicalVector([
                line * adjacency.transpose().matrix[i]
                for i in range(len(line))
            ])
        return TropicalMatrix([
            compute_line(line_idx) 
            for line_idx in range(len(self.matrix))
        ])
    
    def __pow__(self, power: int) -> "TropicalMatrix":
        if power < 1:
            # The identity matrix nor inverses are not defined. Therefore, nonpositive power is not given. 
            raise NotImplementedError()
        elif power == 1:
            return self
        else:
            return self * (self ** (power - 1))
    
    def __str__(self) -> str:
        return str(
            list(map(lambda vec: str(vec), self.matrix))
        )
    
    def transpose(self) -> "TropicalMatrix":
        def compute_line(line_idx: int) -> TropicalVector:
            return TropicalVector([
                self.matrix[i][line_idx]
                for i in range(len(self.matrix))
            ])
        return TropicalMatrix(
            [ compute_line(line_idx)
            for line_idx in range(len(self.matrix[0]))]
        )

A = TropicalMatrix([
    TropicalVector([ Weight(inf), Weight( 2 ), Weight( 4 ), Weight(inf) ]),
    TropicalVector([ Weight(inf), Weight( 0 ), Weight( 1 ), Weight( 9 ) ]),
    TropicalVector([ Weight(inf), Weight(inf), Weight(inf), Weight( 5 ) ]),
    TropicalVector([ Weight( 3 ), Weight(inf), Weight(inf), Weight(inf) ])
])

P = TropicalMatrix([
    TropicalVector([ Path(   None, inf), Path([(1,2)],  2 ), Path([(1,3)],  4 ), Path(   None, inf) ]),
    TropicalVector([ Path(   None, inf), Path([(2,2)],  0 ), Path([(2,3)],  1 ), Path([(2,4)],  9 ) ]),
    TropicalVector([ Path(   None, inf), Path(   None, inf), Path(   None, inf), Path([(3,4)],  5 ) ]),
    TropicalVector([ Path([(4,1)],  3 ), Path(   None, inf), Path(   None, inf), Path(   None, inf) ])
])


if __name__ == "__main__":
    print(A ** 2)
    print(P ** 2)