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

    pub fn delete(&mut self, key: &K) -> Result<V, MapError> {
        let mut deleted_value = None;
        self.root = Self::delete_recursive(self.root.take(), key, &mut deleted_value);
        deleted_value.ok_or(MapError::KeyNotFound)
    }

    fn delete_recursive(node: Option<Box<Node<K, V>>>, key: &K, deleted_value: &mut Option<V>) -> Option<Box<Node<K, V>>> {
        match node {
            None => None,
            Some(mut n) => {
                match key.cmp(&n.key) {
                    std::cmp::Ordering::Less => {
                        n.left = Self::delete_recursive(n.left, key, deleted_value);
                        Some(n)
                    },
                    std::cmp::Ordering::Greater => {
                        n.right = Self::delete_recursive(n.right, key, deleted_value);
                        Some(n)
                    },
                    std::cmp::Ordering::Equal => {
                        *deleted_value = Some(n.value);
                        match (n.left, n.right) {
                            // Case 1: No children - just remove the node
                            (None, None) => None,
                            // Case 2: One child - replace with the child
                            (Some(left), None) => Some(left),
                            (None, Some(right)) => Some(right),
                            // Case 3: Two children - replace with in-order successor
                            (Some(left), Some(right)) => {
                                let (successor_value, successor_key, new_right) = Self::extract_min(right);
                                Some(Box::new(Node {
                                    key: successor_key,
                                    value: successor_value,
                                    left: Some(left),
                                    right: new_right,
                                }))
                            }
                        }
                    }
                }
            }
        }
    }

    fn extract_min(mut node: Box<Node<K, V>>) -> (V, K, Option<Box<Node<K, V>>>) {
        match node.left.take() {
            None => {
                // This node is the minimum
                (node.value, node.key, node.right)
            },
            Some(left) => {
                // Recurse to find minimum in left subtree
                let (min_value, min_key, new_left) = Self::extract_min(left);
                node.left = new_left;
                (min_value, min_key, Some(node))
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

    #[test]
    fn test_delete_from_empty_map() {
        let mut map: BinaryTreeMap<i32, String> = BinaryTreeMap::new();
        let result = map.delete(&42);
        assert_eq!(result, Err(MapError::KeyNotFound));
    }

    #[test]
    fn test_delete_leaf_node() {
        let mut map = BinaryTreeMap::new();
        map.insert(50, "root".to_string());
        map.insert(30, "left".to_string());
        map.insert(70, "right".to_string());
        
        // Delete leaf node
        let result = map.delete(&30);
        assert_eq!(result, Ok("left".to_string()));
        
        // Verify it's gone
        assert_eq!(map.get(&30), Err(MapError::KeyNotFound));
        // Verify others remain
        assert_eq!(map.get(&50), Ok(&"root".to_string()));
        assert_eq!(map.get(&70), Ok(&"right".to_string()));
    }

    #[test]
    fn test_delete_node_with_one_child() {
        let mut map = BinaryTreeMap::new();
        map.insert(50, "root".to_string());
        map.insert(30, "left".to_string());
        map.insert(20, "left-left".to_string());
        
        // Delete node with one child
        let result = map.delete(&30);
        assert_eq!(result, Ok("left".to_string()));
        
        // Verify structure is maintained
        assert_eq!(map.get(&30), Err(MapError::KeyNotFound));
        assert_eq!(map.get(&50), Ok(&"root".to_string()));
        assert_eq!(map.get(&20), Ok(&"left-left".to_string()));
    }

    #[test]
    fn test_delete_node_with_two_children() {
        let mut map = BinaryTreeMap::new();
        map.insert(50, "root".to_string());
        map.insert(30, "left".to_string());
        map.insert(70, "right".to_string());
        map.insert(60, "right-left".to_string());
        map.insert(80, "right-right".to_string());
        
        // Delete node with two children
        let result = map.delete(&70);
        assert_eq!(result, Ok("right".to_string()));
        
        // Verify structure is maintained (successor should replace deleted node)
        assert_eq!(map.get(&70), Err(MapError::KeyNotFound));
        assert_eq!(map.get(&50), Ok(&"root".to_string()));
        assert_eq!(map.get(&30), Ok(&"left".to_string()));
        assert_eq!(map.get(&60), Ok(&"right-left".to_string()));
        assert_eq!(map.get(&80), Ok(&"right-right".to_string()));
    }

    #[test]
    fn test_delete_root_node() {
        let mut map = BinaryTreeMap::new();
        map.insert(50, "root".to_string());
        map.insert(30, "left".to_string());
        map.insert(70, "right".to_string());
        
        // Delete root node
        let result = map.delete(&50);
        assert_eq!(result, Ok("root".to_string()));
        
        // Verify structure is maintained
        assert_eq!(map.get(&50), Err(MapError::KeyNotFound));
        assert_eq!(map.get(&30), Ok(&"left".to_string()));
        assert_eq!(map.get(&70), Ok(&"right".to_string()));
    }

    #[test]
    fn test_delete_nonexistent_key() {
        let mut map = BinaryTreeMap::new();
        map.insert(50, "root".to_string());
        
        let result = map.delete(&99);
        assert_eq!(result, Err(MapError::KeyNotFound));
        
        // Verify original data is untouched
        assert_eq!(map.get(&50), Ok(&"root".to_string()));
    }
}
