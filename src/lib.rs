#[derive(Debug, PartialEq)]
pub enum MapError {
    KeyNotFound,
}

#[derive(Debug)]
struct Node<K, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
}

#[derive(Debug)]
pub struct BinaryTreeMap<K, V> {
    root: Option<Box<Node<K, V>>>,
}

impl<K: Ord, V> BinaryTreeMap<K, V> {
    pub fn new() -> Self {
        BinaryTreeMap { root: None }
    }

    pub fn insert(&mut self, key: K, value: V) {
        self.root = Self::insert_recursive(self.root.take(), key, value);
    }

    fn insert_recursive(node: Option<Box<Node<K, V>>>, key: K, value: V) -> Option<Box<Node<K, V>>> {
        match node {
            None => Some(Box::new(Node {
                key,
                value,
                left: None,
                right: None,
            })),
            Some(mut n) => {
                match key.cmp(&n.key) {
                    std::cmp::Ordering::Equal => {
                        n.value = value; // Update existing value
                        Some(n)
                    },
                    std::cmp::Ordering::Less => {
                        n.left = Self::insert_recursive(n.left, key, value);
                        Some(n)
                    },
                    std::cmp::Ordering::Greater => {
                        n.right = Self::insert_recursive(n.right, key, value);
                        Some(n)
                    },
                }
            }
        }
    }

    pub fn get(&self, key: &K) -> Result<&V, MapError> {
        self.get_recursive(&self.root, key)
    }

    fn get_recursive<'a>(&self, node: &'a Option<Box<Node<K, V>>>, key: &K) -> Result<&'a V, MapError> {
        match node {
            None => Err(MapError::KeyNotFound),
            Some(n) => {
                match key.cmp(&n.key) {
                    std::cmp::Ordering::Equal => Ok(&n.value),
                    std::cmp::Ordering::Less => self.get_recursive(&n.left, key),
                    std::cmp::Ordering::Greater => self.get_recursive(&n.right, key),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_map_returns_error() {
        let map: BinaryTreeMap<i32, String> = BinaryTreeMap::new();
        let result = map.get(&42);
        assert_eq!(result, Err(MapError::KeyNotFound));
    }

    #[test]
    fn test_insert_and_retrieve() {
        let mut map = BinaryTreeMap::new();
        map.insert(42, "hello".to_string());
        let result = map.get(&42);
        assert_eq!(result, Ok(&"hello".to_string()));
    }
}
